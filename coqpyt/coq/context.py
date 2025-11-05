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

        # For versions 8.18+, we ignore the tags [VernacSynterp] and [VernacSynPure]
        # and use the "ntn_decl" prefix when handling where notations
        post17 = version.parse(coq_version) >= version.parse("8.18")
        self.__expr = lambda e: e[1] if post17 else e
        self.__where_notation_key = "ntn_decl" if post17 else "decl_ntn"

        # For versions 8.19+, VernacExtend has a dictionary instead of a list in the
        # AST, so we use "ext_plugin","ext_entry" and "ext_index" instead of indices
        post18 = version.parse(coq_version) >= version.parse("8.19")
        self.__ext_plugin = lambda e: e["ext_plugin"] if post18 else None
        self.__ext_entry = lambda e: e["ext_entry"] if post18 else e[0]
        # FIXME: This should be made private once [__get_program_context] is extracted
        # from ProofFile to here.
        self.ext_index = lambda e: e["ext_index"] if post18 else e[1]

        # For versions 9.0+, the AST structure for fixpoints changed
        rocq = version.parse(coq_version) >= version.parse("9.0")
        self.__fixpoint_notations = lambda e: (
            []
            if len(e) < 3 or not isinstance(e[2], list)
            else (
                e[2][1][0]["notations"]
                if (
                    rocq
                    and len(e[2]) > 1
                    and isinstance(e[2][1], list)
                    and len(e[2][1]) > 0
                    and isinstance(e[2][1][0], dict)
                    and "notations" in e[2][1][0]
                    and isinstance(e[2][1][0]["notations"], list)
                )
                else (
                    e[2][0]["notations"]
                    if (
                        not rocq
                        and len(e[2]) > 0
                        and isinstance(e[2][0], dict)
                        and "notations" in e[2][0]
                        and isinstance(e[2][0]["notations"], list)
                    )
                    else []
                )
            )
        )

        # We only tested versions 8.17 to 9.0, so we provide no claims about
        # versions prior to that.

    def __init_context(self, terms: Optional[Dict[str, Term]] = None):
        # NOTE: We use a stack for each term because of the following case:
        # 1) File A imports a file B with term C
        # 2) File A defines a new term C
        self.__terms: Dict[str, List[Term]] = {} if terms is None else terms
        self.__last_terms: List[Tuple[str, Term]] = []
        self.__segments = SegmentStack()
        self.__anonymous_id: Optional[int] = None

    def __repr__(self) -> str:
        res = ""
        for name, terms in self.__terms.items():
            res += f"{name}: {repr(terms[-1])}\n"
        return res

    def __add_terms(self, step: Step, expr: List):
        term_type = self.__term_type(expr)
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

        if self.__is_extend(expr, "VernacTacticNotation"):
            # FIXME: Handle this case
            return
        elif expr[0] == "VernacNotation":
            name = re.split("Notation |Infix ", text)[1].split('"')[1].strip()
            if text[:-1].split(":")[-1].endswith("_scope"):
                name += " : " + text[:-1].split(":")[-1].strip()
            self.__add_term(name, step, TermType.NOTATION)
        elif expr[0] == "VernacSyntacticDefinition":
            name = text.split("Notation ")[1].split(" ")[0]
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
            for arg in expr[2]:
                name = FileContext.get_ident(arg)
                if name is not None:
                    self.__add_term(name, step, term_type)
        elif term_type in [TermType.OBLIGATION, TermType.EQUATION]:
            # FIXME: For Equations, we are unable of getting terms from the AST
            # but these commands do generate named terms
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

        # Terms that are not part of the accessible context (e.g. obligations),
        # but are still registered in last_terms.
        if name == "":
            return

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
        elif term_type == TermType.FIXPOINT:
            spans = self.__fixpoint_notations(expr)

        # handles when multiple notations are defined
        for span in spans:
            name = FileContext.__get_notation_key(
                span[f"{self.__where_notation_key}_string"]["v"],
                span[f"{self.__where_notation_key}_scope"],
            )
            self.__add_term(name, step, TermType.NOTATION)

    def __is_extend(
        self, expr: List, entry: str | Tuple[str], exact: bool = True
    ) -> bool:
        if expr[0] != "VernacExtend":
            return False
        if exact:
            return self.__ext_entry(expr[1]) == entry
        return self.__ext_entry(expr[1]).startswith(entry)

    def __term_type(self, expr: List) -> TermType:
        if expr[0] == "VernacStartTheoremProof":
            return getattr(TermType, expr[1][0].upper())
        if expr[0] == "VernacDefinition":
            return TermType.DEFINITION
        if expr[0] in ["VernacNotation", "VernacSyntacticDefinition"]:
            return TermType.NOTATION
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
        # FIXME: These are plugins and should probably be handled differently
        if self.__is_extend(expr, "Obligations"):
            return TermType.OBLIGATION
        if self.__is_extend(expr, "VernacDeclareTacticDefinition"):
            return TermType.TACTIC
        if self.__is_extend(expr, "Function"):
            return TermType.FUNCTION
        if self.__is_extend(expr, "Define_equations", exact=False):
            return TermType.EQUATION
        if self.__is_extend(expr, "Derive", exact=False):
            return TermType.DERIVE
        if self.__is_extend(expr, "AddSetoid", exact=False):
            return TermType.SETOID
        if self.__is_extend(
            expr, ("AddRelation", "AddParametricRelation"), exact=False
        ):
            return TermType.RELATION
        return TermType.OTHER

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
    def is_id(el) -> bool:
        return isinstance(el, list) and (len(el) == 3 and el[0] == "Ser_Qualid")

    @staticmethod
    def is_notation(el) -> bool:
        return isinstance(el, list) and (
            len(el) == 4 and el[0] == "CNotation" and el[2][1] != ""
        )

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
        # FIXME: This method should be made private once [__get_program_context]
        # is extracted from ProofFile to here.
        def handle_arg_type(args, ids):
            if args[0] == "ExtraArg":
                if args[1] == "identref":
                    return ids[0][1][1]
                elif args[1] == "ident":
                    return ids[1]
            return None

        if len(el) == 3 and el[0] == "GenArg" and el[1][0] == "Rawwit":
            return handle_arg_type(el[1][1], el[2])
        return None

    @staticmethod
    def __get_v(el: List) -> Optional[str]:
        if isinstance(el, dict) and "v" in el:
            return el["v"]
        elif isinstance(el, list) and len(el) == 2 and el[0] == "v":
            return el[1]
        return None

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
            or self.__is_extend(expr, "VernacSolve")
        ):
            return

        # Keep track of current segments
        if expr[0] == "VernacEndSegment":
            self.__segments.go_back()
        elif expr[0] == "VernacDefineModule" and len(expr[-1]) == 0:
            self.__segments.push(expr[2]["v"][1], SegmentType.MODULE)
        elif expr[0] == "VernacDeclareModuleType" and len(expr[-1]) == 0:
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
        elif expr[0] == "VernacDefineModule" and len(expr[-1]) == 0:
            self.__segments.pop()
        elif expr[0] == "VernacDeclareModuleType" and len(expr[-1]) == 0:
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

    def attrs(self, step: Step) -> List:
        """
        Args:
            step (Step): The step to be processed.

        Returns:
            List: 'attrs' field from the AST of a step.
        """
        if (
            step.ast.span is not None
            and isinstance(step.ast.span, dict)
            and "v" in step.ast.span
            and isinstance(step.ast.span["v"], dict)
            and "attrs" in step.ast.span["v"]
        ):
            return step.ast.span["v"]["attrs"]
        return []

    def term_type(self, step: Step) -> TermType:
        """
        Args:
            step (Step): The step to be processed.

        Returns:
            TermType: The term type of the step.
        """
        return self.__term_type(self.expr(step))

    def is_proof_term(self, step: Step) -> bool:
        """
        Args:
            step (Step): The step to be processed.

        Returns:
            bool: Whether the step introduces a new proof term.
        """
        term_type = self.term_type(step)
        # Assume that terms of the following types do not introduce new proofs
        # FIXME: Should probably check if goals were changed
        return term_type not in [
            TermType.TACTIC,
            TermType.NOTATION,
            TermType.INDUCTIVE,
            TermType.COINDUCTIVE,
            TermType.RECORD,
            TermType.CLASS,
            TermType.SCHEME,
            TermType.VARIANT,
            TermType.OTHER,
        ]

    def is_end_proof(self, step: Step) -> bool:
        """
        Args:
            step (Step): The step to be processed.

        Returns:
            bool: Whether the step closes an open proof term.
        """
        # FIXME: Refer to issue #55: https://github.com/sr-lab/coqpyt/issues/55
        expr = self.expr(step)[0]
        return expr in ["VernacEndProof", "VernacExactProof", "VernacAbort"]

    def is_segment_delimiter(self, step: Step) -> bool:
        """
        Args:
            step (Step): The step to be processed.

        Returns:
            bool: Whether the step delimits a segment (module or section).
        """
        expr = self.expr(step)[0]
        return expr in [
            "VernacEndSegment",
            "VernacDefineModule",
            "VernacDeclareModuleType",
            "VernacBeginSection",
        ]

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

    @staticmethod
    def get_notation_scope(notation: str) -> str:
        """Get the scope of a notation.
        Args:
            notation (str): Possibly scoped notation pattern. E.g. "_ + _ : nat_scope".

        Returns:
            str: The scope of the notation. E.g. "nat_scope".
        """
        if notation.split(":")[-1].endswith("_scope"):
            return notation.split(":")[-1].strip()
        return ""

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

        def get_regex(notation_id):
            regex = f"{re.escape(notation_id)}".split("\\ ")
            regex = [sub for sub in regex if sub != ""]
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
            # The */+ allows to have any amount of spaces between the words
            # because it does not matter for the notation
            regex = "^\\ *" + "\\ +".join(regex) + "\\ *$"
            return regex

        notation_id = FileContext.__get_notation_key(notation, scope)
        regex = get_regex(notation_id)
        unscoped_regex = get_regex(notation)

        # Search notations
        match_unscoped, match_unscoped_regex = None, None
        for term in self.__terms.keys():
            if re.match(regex, term):
                return self.__terms[term][-1]
            if re.match(unscoped_regex, term):
                match_unscoped_regex = term
            # We can't use split because : may be used in the notation
            if re.match(regex, term.rsplit(":", 1)[0].strip()):
                match_unscoped = term

        # In case the stored id does not contain the scope and no scope matched/was provided
        if match_unscoped_regex is not None:
            return self.__terms[match_unscoped_regex][-1]
        # In case the stored id contains the scope and no scope matched/was provided
        elif match_unscoped is not None:
            return self.__terms[match_unscoped][-1]

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
