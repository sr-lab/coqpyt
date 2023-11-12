import re
import subprocess
from packaging import version
from typing import Optional, List, Dict

from coqpyt.coq.exceptions import NotationNotFoundException
from coqpyt.coq.structs import SegmentType, SegmentStack, Step, TermType, Term


class FileContext:
    def __init__(
        self,
        path: str,
        module: Optional[List[str]] = None,
        coqtop: str = "coqtop",
        terms: Optional[Dict[str, Term]] = None,
    ):
        self.path = path
        self.module = [] if module is None else module
        self.__init_coq_version(coqtop)
        self.terms = {} if terms is None else terms
        self.last_term: Optional[Term] = None
        self.__segments = SegmentStack()
        self.__anonymous_id: Optional[int] = None

    def __init_coq_version(self, coqtop):
        output = subprocess.check_output(f"{coqtop} -v", shell=True)
        coq_version = output.decode("utf-8").split("\n")[0].split()[-1]
        outdated = version.parse(coq_version) < version.parse("8.18")

        # For version 8.18, we ignore the tags [VernacSynterp] and [VernacSynPure]
        # and use the "ntn_decl" prefix when handling where notations
        # For older versions, we only tested 8.17, so we provide no claims about
        # versions prior to that.

        self.__expr = lambda e: e if outdated else e[1]
        self.__where_notation_key = "decl_ntn" if outdated else "ntn_decl"

    def __add_terms(self, step: Step, expr: List):
        term_type = FileContext.__term_type(expr)
        text = step.short_text

        # FIXME: Section-local terms are ignored. We do this to avoid
        # overwriting global terms with section-local terms after the section
        # is closed. Regardless, these should be handled given that they might
        # be used within the section.
        for keyword in [
            "Variable",
            "Let",
            "Context",
            "Hypothesis",
            "Hypotheses",
        ]:
            if text.startswith(keyword):
                # NOTE: We update the last term so as to obtain proofs even for
                # section-local terms. This is safe, because the attribute is
                # meant to be overwritten every time a new term is found.
                self.last_term = Term(
                    step, term_type, self.path, self.__segments.modules[:]
                )
                return

        if expr[0] == "VernacExtend" and expr[1][0] == "VernacTacticNotation":
            # FIXME: Handle this case
            return
        elif expr[0] == "VernacNotation":
            name = text.split('"')[1].strip()
            if text[:-1].split(":")[-1].endswith("_scope"):
                name += " : " + text[:-1].split(":")[-1].strip()
            self.__add_term(name, step, TermType.NOTATION)
        elif expr[0] == "VernacSyntacticDefinition":
            name = text.split(" ")[1]
            if text[:-1].split(":")[-1].endswith("_scope"):
                name += " : " + text[:-1].split(":")[-1].strip()
            self.__add_term(name, step, TermType.NOTATION)
        elif expr[0] == "VernacInstance" and expr[1][0]["v"][0] == "Anonymous":
            # FIXME: The name should be "<Class>_instance_N"
            self.__add_term("_anonymous", step, term_type)
        elif expr[0] == "VernacDefinition" and expr[2][0]["v"][0] == "Anonymous":
            # We associate the anonymous term to the same name used internally by Coq
            if self.__anonymous_id is None:
                name, self.__anonymous_id = "Unnamed_thm", 0
            else:
                name = f"Unnamed_thm{self.__anonymous_id}"
                self.__anonymous_id += 1
            self.__add_term(name, step, term_type)
        elif term_type == TermType.DERIVE:
            name = FileContext.get_ident(expr[2][0])
            self.__add_term(name, step, term_type)
            if expr[1][0] == "Derive":
                prop = FileContext.get_ident(expr[2][2])
                self.__add_term(prop, step, term_type)
        elif term_type == TermType.OBLIGATION:
            self.last_term = Term(step, term_type, self.path, self.__segments.modules[:])
        else:
            names = FileContext.__get_names(expr)
            for name in names:
                self.__add_term(name, step, term_type)

        self.__handle_where_notations(step, expr, term_type)

    def __add_term(self, name: str, step: Step, term_type: TermType):
        modules = self.__segments.modules[:]
        term = Term(step, term_type, self.path, modules)
        self.last_term = term
        if term.type == TermType.NOTATION:
            self.terms[name] = term
            return

        self.terms[".".join(modules + [name])] = term

        curr_module = ""
        for module in reversed(self.module):
            curr_module = module + "." + curr_module
            self.terms[curr_module + name] = term

    # Simultaneous definition of terms and notations (where clause)
    # https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#simultaneous-definition-of-terms-and-notations
    def __handle_where_notations(self, step: Step, expr: List, term_type: TermType):
        spans = []
        if (
            term_type
            in [
                TermType.VARIANT,
                TermType.INDUCTIVE,
            ]
            and len(expr) > 2
            and isinstance(expr[2], list)
            and len(expr[2]) > 0
            and isinstance(expr[2][0], list)
            and len(expr[2][0]) > 1
            and isinstance(expr[2][0][1], list)
            and len(expr[2][0][1]) > 0
        ):
            spans = expr[2][0][1]
        elif (
            term_type == TermType.FIXPOINT
            and len(expr) > 2
            and isinstance(expr[2], list)
            and len(expr[2]) > 0
            and isinstance(expr[2][0], dict)
            and "notations" in expr[2][0]
            and isinstance(expr[2][0]["notations"], list)
            and len(expr[2][0]["notations"]) > 0
        ):
            spans = expr[2][0]["notations"]

        # handles when multiple notations are defined
        for span in spans:
            name = FileContext.get_notation_key(
                span[f"{self.__where_notation_key}_string"]["v"],
                span[f"{self.__where_notation_key}_scope"],
            )
            self.__add_term(name, step, TermType.NOTATION)

    @staticmethod
    def __get_names(expr: List) -> List[str]:
        inductive = expr[0] == "VernacInductive"
        extend = expr[0] == "VernacExtend"
        stack, res = expr[:0:-1], []
        while len(stack) > 0:
            el = stack.pop()
            v = FileContext.get_v(el)
            if v is not None and isinstance(v, list) and len(v) == 2:
                id = FileContext.get_id(v)
                if id is not None:
                    if not inductive:
                        return [id]
                    res.append(id)
                elif v[0] == "Name":
                    if not inductive:
                        return [v[1][1]]
                    res.append(v[1][1])

            elif isinstance(el, dict):
                for v in reversed(el.values()):
                    if isinstance(v, (dict, list)):
                        stack.append(v)
            elif isinstance(el, list):
                if len(el) > 0 and el[0] == "CLocalAssum":
                    continue

                ident = FileContext.get_ident(el)
                if ident is not None and extend:
                    return [ident]

                for v in reversed(el):
                    if isinstance(v, (dict, list)):
                        stack.append(v)
        return res

    @staticmethod
    def __term_type(expr: List) -> TermType:
        if expr[0] == "VernacStartTheoremProof":
            return getattr(TermType, expr[1][0].upper())
        if expr[0] == "VernacDefinition":
            return TermType.DEFINITION
        if expr[0] in ["VernacNotation", "VernacSyntacticDefinition"]:
            return TermType.NOTATION
        if expr[0] == "VernacExtend" and expr[1][0] == "Obligations":
            return TermType.OBLIGATION
        if expr[0] == "VernacInductive" and expr[1][0] == "Class":
            return TermType.CLASS
        if expr[0] == "VernacInductive" and expr[1][0] in ["Record", "Structure"]:
            return TermType.RECORD
        if expr[0] == "VernacInductive" and expr[1][0] == "Variant":
            return TermType.VARIANT
        if expr[0] == "VernacInductive" and expr[1][0] == "CoInductive":
            return TermType.COINDUCTIVE
        if expr[0] == "VernacInductive":
            return TermType.INDUCTIVE
        if expr[0] == "VernacInstance":
            return TermType.INSTANCE
        if expr[0] == "VernacCoFixpoint":
            return TermType.COFIXPOINT
        if expr[0] == "VernacFixpoint":
            return TermType.FIXPOINT
        if expr[0] == "VernacScheme":
            return TermType.SCHEME
        if expr[0] == "VernacExtend" and expr[1][0].startswith("Derive"):
            return TermType.DERIVE
        if expr[0] == "VernacExtend" and expr[1][0].startswith("AddSetoid"):
            return TermType.SETOID
        if expr[0] == "VernacExtend" and expr[1][0].startswith(
            ("AddRelation", "AddParametricRelation")
        ):
            return TermType.RELATION
        if expr[0] == "VernacExtend" and expr[1][0] == "VernacDeclareTacticDefinition":
            return TermType.TACTIC
        if expr[0] == "VernacExtend" and expr[1][0] == "Function":
            return TermType.FUNCTION
        return TermType.OTHER

    @property
    def local_terms(self) -> List[Term]:
        """
        Returns:
            List[Term]: The executed terms defined in the current file.
        """
        return list(
            filter(lambda term: term.file_path == self.path, self.terms.values())
        )

    @property
    def in_module_type(self) -> bool:
        return len(self.__segments.module_types) > 0

    def process_step(self, step: Step):
        expr = self.expr(step)
        if (
            expr == [None]
            or expr[0] == "VernacProof"
            or (expr[0] == "VernacExtend" and expr[1][0] == "VernacSolve")
        ):
            return

        # Keep track of current segments
        if expr[0] == "VernacEndSegment":
            self.__segments.pop()
        elif expr[0] == "VernacDefineModule":
            self.__segments.push(expr[2]["v"][1], SegmentType.MODULE)
        elif expr[0] == "VernacDeclareModuleType":
            self.__segments.push(expr[1]["v"][1], SegmentType.MODULE_TYPE)
        elif expr[0] == "VernacBeginSection":
            self.__segments.push(expr[1]["v"][1], SegmentType.SECTION)
        # HACK: We ignore terms inside a Module Type since they can't be used outside
        # and should be overriden.
        elif not self.in_module_type:
            self.__add_terms(step, expr)

    def expr(self, step: Step) -> Optional[List]:
        if (
            step.ast.span is not None
            and isinstance(step.ast.span, dict)
            and "v" in step.ast.span
            and isinstance(step.ast.span["v"], dict)
            and "expr" in step.ast.span["v"]
        ):
            return self.__expr(step.ast.span["v"]["expr"])
        return [None]

    def term_type(self, step: Step) -> TermType:
        return FileContext.__term_type(self.expr(step))

    def update(self, terms: Dict[str, Term] = {}):
        self.terms.update(terms)

    def append_module_prefix(self, name: str) -> str:
        return ".".join(self.__segments.modules + [name])

    def get_term(self, name: str) -> Optional[Term]:
        for i in range(len(self.__segments.modules), -1, -1):
            curr_name = ".".join(self.__segments.modules[:i] + [name])
            if curr_name in self.terms:
                return self.terms[curr_name]
        return None

    def get_notation(self, notation: str, scope: str) -> Term:
        """Get a notation from the context.

        Args:
            notation (str): Id of the notation. E.g. "_ + _"
            scope (str): Scope of the notation. E.g. "nat_scope"

        Raises:
            RuntimeError: If the notation is not found in the context.

        Returns:
            Term: Term that corresponds to the notation.
        """
        notation_id = FileContext.get_notation_key(notation, scope)
        regex = f"{re.escape(notation_id)}".split("\\ ")
        for i, sub in enumerate(regex):
            if sub == "_":
                # We match the wildcard with the description from here:
                # https://coq.inria.fr/distrib/current/refman/language/core/basic.html#grammar-token-ident
                # Coq accepts more characters, but no one should need more than these...
                chars = "A-Za-zÀ-ÖØ-öø-ˁˆ-ˑˠ-ˤˬˮͰ-ʹͶͷͺ-ͽͿΆΈ-ΊΌΎ-ΡΣ-ϵϷ-ҁҊ-ԯԱ-Ֆՙա-և"
                regex[i] = f"([{chars}][{chars}0-9_']*|_[{chars}0-9_']+)"
            else:
                # Handle '_'
                regex[i] = f"({sub}|('{sub}'))"
        regex = "^" + "\\ ".join(regex) + "$"

        # Search notations
        unscoped = None
        for term in self.terms.keys():
            if re.match(regex, term):
                return self.terms[term]
            if re.match(regex, term.split(":")[0].strip()):
                unscoped = term
        # In case the stored id contains the scope but no scope is provided
        if unscoped is not None:
            return self.terms[unscoped]

        # Search Infix
        if re.match("^_ ([^ ]*) _$", notation):
            op = notation[2:-2]
            key = FileContext.get_notation_key(op, scope)
            if key in self.terms:
                return self.terms[key]

        raise NotationNotFoundException(notation_id)

    @staticmethod
    def get_notation_key(notation: str, scope: str) -> str:
        if scope != "" and scope is not None:
            notation += " : " + scope
        return notation

    @staticmethod
    def get_id(id: List) -> Optional[str]:
        if id[0] == "Ser_Qualid":
            return ".".join([l[1] for l in reversed(id[1][1])] + [id[2][1]])
        elif id[0] == "Id":
            return id[1]
        return None

    @staticmethod
    def get_ident(el: List) -> Optional[str]:
        if (
            len(el) == 3
            and el[0] == "GenArg"
            and el[1][0] == "Rawwit"
            and el[1][1][0] == "ExtraArg"
        ):
            if el[1][1][1] == "identref":
                return el[2][0][1][1]
            elif el[1][1][1] == "ident":
                return el[2][1]
        return None

    @staticmethod
    def get_v(el: List) -> Optional[str]:
        if isinstance(el, dict) and "v" in el:
            return el["v"]
        elif isinstance(el, list) and len(el) == 2 and el[0] == "v":
            return el[1]
        return None
