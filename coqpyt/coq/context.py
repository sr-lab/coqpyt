import re
import subprocess
from packaging import version
from typing import Optional, List, Dict, Tuple, Union

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
        self.libraries: Dict[str, Dict[str, Term]] = {}
        self.__path = path
        self.__module = [] if module is None else module
        self.__init_coq_version(coqtop)
        self.__init_context(terms)

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

    def __init_context(self, terms: Optional[Dict[str, Term]] = None):
        # NOTE: We use a stack for each term because of the following case:
        # 1) File A imports a file B with term C
        # 2) File A defines a new term C
        self.__terms: Dict[str, List[Term]] = {} if terms is None else terms
        self.__last_terms: List[Tuple[str, Term]] = []
        self.__segments = SegmentStack()
        self.__anonymous_id: Optional[int] = None

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
                self.__last_terms[-1].append(
                    ("", Term(step, term_type, self.__path, self.__segments.modules[:]))
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
            self.__last_terms[-1].append(
                ("", Term(step, term_type, self.__path, self.__segments.modules[:]))
            )
        else:
            names = FileContext.__get_names(expr)
            for name in names:
                self.__add_term(name, step, term_type)

        self.__handle_where_notations(step, expr, term_type)

    def __add_term(self, name: str, step: Step, term_type: TermType):
        def check_and_add_term(name, term):
            if name not in self.__terms:
                self.__terms[name] = []
            self.__terms[name].append(term)

        modules = self.__segments.modules[:]
        term = Term(step, term_type, self.__path, modules)
        self.__last_terms[-1].append((name, term))
        if term.type == TermType.NOTATION:
            check_and_add_term(name, term)
            return

        # The modules inside the file are handled by the get_term method
        # so we don't have to worry about them here.
        check_and_add_term(".".join(modules + [name]), term)

        curr_module = ""
        for module in reversed(self.__module):
            curr_module = module + "." + curr_module
            check_and_add_term(curr_module + name, term)

    def __remove_term(self, name: str, term: Term):
        def remove_term(name):
            self.__terms[name].pop()
            if len(self.__terms[name]) == 0:
                del self.__terms[name]

        if term.type == TermType.NOTATION:
            remove_term(name)
            return

        modules = self.__segments.modules[:]
        remove_term(".".join(modules + [name]))

        curr_module = ""
        for module in reversed(self.__module):
            curr_module = module + "." + curr_module
            remove_term(curr_module + name)

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
            name = FileContext.__get_notation_key(
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
            v = FileContext.__get_v(el)
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
    def get_id(id: List) -> Optional[str]:
        # FIXME: This should be made private once [__step_context] is extracted
        # from ProofFile to here.
        if id[0] == "Ser_Qualid":
            return ".".join([l[1] for l in reversed(id[1][1])] + [id[2][1]])
        elif id[0] == "Id":
            return id[1]
        return None

    @staticmethod
    def get_ident(el: List) -> Optional[str]:
        # FIXME: This should be made private once [__get_program_context] is extracted
        # from ProofFile to here.
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
    def __get_v(el: List) -> Optional[str]:
        if isinstance(el, dict) and "v" in el:
            return el["v"]
        elif isinstance(el, list) and len(el) == 2 and el[0] == "v":
            return el[1]
        return None

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

    @staticmethod
    def __get_notation_key(notation: str, scope: str) -> str:
        if scope != "" and scope is not None:
            notation += " : " + scope
        return notation

    @property
    def local_terms(self) -> List[Term]:
        """
        Returns:
            List[Term]: The executed terms defined in the current file.
        """
        return list(
            filter(lambda term: term.file_path == self.__path, self.terms.values())
        )

    @property
    def terms(self) -> Dict[str, Term]:
        """
        Returns:
            Dict[str, Term]: All terms defined in the current file.
        """
        defined_terms = {}
        for name, terms in self.__terms.items():
            defined_terms[name] = terms[-1]
        return defined_terms

    @property
    def in_module_type(self) -> bool:
        """
        Returns:
            bool: True if currently inside a module type.
        """
        return len(self.__segments.module_types) > 0

    @property
    def last_term(self) -> Optional[Term]:
        """
        Returns:
            Optional[Term]: The last term defined in the current file.
        """
        for terms in self.__last_terms[::-1]:
            if len(terms) > 0:
                return terms[-1][1]
        return None

    @property
    def curr_modules(self) -> List[str]:
        """
        Returns:
            List[str]: The current module path.
        """
        return self.__segments.modules[:]

    def process_step(self, step: Step):
        """Extracts the identifiers from a step and updates the context with
        new terms defined by the step.

        Args:
            step (Step): The step to be processed.
        """
        expr = self.expr(step)
        self.__last_terms.append([])
        if (
            expr == [None]
            or expr[0] == "VernacProof"
            or (expr[0] == "VernacExtend" and expr[1][0] == "VernacSolve")
        ):
            return

        # Keep track of current segments
        if expr[0] == "VernacEndSegment":
            self.__segments.go_back()
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

    def undo_step(self, step: Step):
        """Removes the terms defined by a step from the context.

        Args:
            step (Step): The step to be reverted.
        """
        expr = self.expr(step)
        terms = self.__last_terms.pop()

        # Keep track of current segments
        if expr[0] == "VernacEndSegment":
            self.__segments.go_forward(expr[1]["v"][1])
        elif expr[0] == "VernacDefineModule":
            self.__segments.pop()
        elif expr[0] == "VernacDeclareModuleType":
            self.__segments.pop()
        elif expr[0] == "VernacBeginSection":
            self.__segments.pop()

        for name, term in terms:
            self.__remove_term(name, term)

    def expr(self, step: Step) -> List:
        """
        Args:
            step (Step): The step to be processed.

        Returns:
            List: 'expr' field from the AST of a step.
        """
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
        """
        Args:
            step (Step): The step to be processed.

        Returns:
            List: The term type of the step.
        """
        return FileContext.__term_type(self.expr(step))

    def update(self, context: Union["FileContext", Dict[str, Term]] = {}):
        """Updates the context with new terms.

        Args:
            terms (Dict[str, Term]): The new terms to be added.
        """
        if isinstance(context, FileContext):
            terms = context.terms
            for library in context.libraries:
                self.add_library(library, context.libraries[library])
        else:
            terms = context

        for name, term in terms.items():
            if name not in self.__terms:
                self.__terms[name] = []
            self.__terms[name].append(term)

    def add_library(self, name: str, terms: Dict[str, Term]):
        """Adds a library to the context.

        Args:
            name (str): The name of the library.
            terms (List[Term]): The terms defined by the library.
        """
        self.libraries[name] = terms
        self.update(terms)

    def remove_library(self, name: str):
        """Removes a library from the context.

        Args:
            name (str): The name of the library.
        """
        if name in self.libraries:
            for term_name, term in self.libraries[name].items():
                self.__remove_term(term_name, term)
            del self.libraries[name]
        else:
            raise RuntimeError(f"Library {name} not found.")

    def append_module_prefix(self, name: str) -> str:
        """Attaches the current module path to the start of a name.

        Args:
            name (str): The name.

        Returns:
            str: The full name with the module path.
        """
        return ".".join(self.__segments.modules + [name])

    def get_term(self, name: str) -> Optional[Term]:
        """Get a notation from the context.

        Args:
            name (str): The term name.

        Returns:
            Optional[Term]: The term mapped to the name, if it exists.
        """
        for i in range(len(self.__segments.modules), -1, -1):
            curr_name = ".".join(self.__segments.modules[:i] + [name])
            if curr_name in self.__terms:
                return self.__terms[curr_name][-1]
        return None

    def get_notation(self, notation: str, scope: str) -> Term:
        """Get a notation from the context.

        Args:
            notation (str): Id of the notation. E.g. "_ + _".
            scope (str): Scope of the notation. E.g. "nat_scope".

        Raises:
            RuntimeError: If the notation is not found in the context.

        Returns:
            Term: Term that corresponds to the notation.
        """
        notation_id = FileContext.__get_notation_key(notation, scope)
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
        for term in self.__terms.keys():
            if re.match(regex, term):
                return self.__terms[term][-1]
            if re.match(regex, term.split(":")[0].strip()):
                unscoped = term
        # In case the stored id contains the scope but no scope is provided
        if unscoped is not None:
            return self.__terms[unscoped][-1]

        # Search Infix
        if re.match("^_ ([^ ]*) _$", notation):
            op = notation[2:-2]
            key = FileContext.__get_notation_key(op, scope)
            if key in self.__terms:
                return self.__terms[key][-1]

        raise NotationNotFoundException(notation_id)

    def reset(self):
        """Resets the context to its initial state."""
        self.__init_context()
