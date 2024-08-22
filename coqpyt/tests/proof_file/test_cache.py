from utility import *
import ipdb

from coqpyt.coq.structs import Term
from coqpyt.coq.proof_file import ProofFile


class TestCache:

    @staticmethod
    def term_files_eq(terms1: dict[str, Term], terms2: dict[str, Term]) -> bool:
        if len(terms1) != len(terms2):
            return False
        for key in terms1:
            if key not in terms2:
                return False
            term1 = terms1[key]
            term2 = terms2[key]
            if term1 != term2:
                return False
            if term1.file_path != term2.file_path:
                return False
        return True

    def test_cache(self):
        with ProofFile(
            "tests/resources/test_imports/test_import.v",
            workspace="tests/resources/test_import",
            use_disk_cache=False,
        ) as pf:
            pf.run()
            no_cache_terms = pf.context.terms.copy()
            no_cache_libs = pf.context.libraries.copy()

        with ProofFile(
            "tests/resources/test_imports/test_import.v",
            workspace="tests/resources/test_import",
            use_disk_cache=True,
        ) as pf:
            pf.run()
            cache1_terms = pf.context.terms.copy()
            cache1_libs = pf.context.libraries.copy()

        with ProofFile(
            "tests/resources/test_imports/test_import.v",
            workspace="tests/resources/test_import",
            use_disk_cache=True,
        ) as pf:
            pf.run()
            cache2_terms = pf.context.terms.copy()
            cache2_libs = pf.context.libraries.copy()

        with ProofFile(
            "tests/resources/test_imports_copy/test_import.v",
            workspace="tests/resources/test_import_copy/",
            use_disk_cache=True,
        ) as pf:
            pf.run()
            cache3_terms = pf.context.terms.copy()
            cache3_libs = pf.context.libraries.copy()

        with ProofFile(
            "tests/resources/test_imports_copy/test_import.v",
            workspace="tests/resources/test_import_copy/",
            use_disk_cache=True,
        ) as pf:
            pf.run()
            cache4_terms = pf.context.terms.copy()
            cache4_libs = pf.context.libraries.copy()

        assert self.term_files_eq(no_cache_terms, cache1_terms)
        assert self.term_files_eq(cache1_terms, cache2_terms)
        assert not self.term_files_eq(cache2_terms, cache3_terms)
        assert self.term_files_eq(cache3_terms, cache4_terms)


if __name__ == "__main__":
    test = TestCache()
    test.test_cache()
