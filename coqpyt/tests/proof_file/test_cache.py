from utility import *


class TestCache(SetupProofFile):
    def setup_method(self, method):
        self.setup(
            "test_imports/test_import.v",
            workspace="test_imports/",
            use_disk_cache=False,
        )
        self.no_cache_terms = self.proof_file.context.terms.copy()
        self.no_cache_libs = self.proof_file.context.libraries.copy()
        self.teardown_method(method)

        self.setup(
            "test_imports/test_import.v",
            workspace="test_imports/",
            use_disk_cache=True,
        )
        self.cache1_terms = self.proof_file.context.terms.copy()
        self.cache1_libs = self.proof_file.context.libraries.copy()
        self.teardown_method(method)

        self.setup(
            "test_imports/test_import.v",
            workspace="test_imports/",
            use_disk_cache=True,
        )
        self.cache2_terms = self.proof_file.context.terms.copy()
        self.cache2_libs = self.proof_file.context.libraries.copy()

    def test_cache(self):
        assert self.no_cache_terms == self.cache1_terms
        assert self.cache1_terms == self.cache2_terms

        assert self.no_cache_libs == self.cache1_libs
        assert self.cache1_libs == self.cache2_libs
