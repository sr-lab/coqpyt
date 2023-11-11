import re
from typing import List, Dict

from coqpyt.coq.structs import Term, CoqError, CoqErrorCodes


class FileContext:
    def __init__(self, path: str, terms: Dict[str, Term] = None):
        self.path = path
        self.terms = {} if terms is None else terms

    @property
    def local_terms(self) -> List[Term]:
        """
        Returns:
            List[Term]: The executed terms defined in the current file.
        """
        return list(
            filter(lambda term: term.file_path == self.path, self.terms.values())
        )

    def update(
        self,
        terms: Dict[str, Term] = {},
    ):
        self.terms.update(terms)

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

        raise CoqError(
            CoqErrorCodes.NotationNotFound,
            f"Notation not found in context: {notation_id}",
        )

    @staticmethod
    def get_notation_key(notation: str, scope: str):
        if scope != "" and scope is not None:
            notation += " : " + scope
        return notation
