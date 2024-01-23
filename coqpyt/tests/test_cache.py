from coqpyt.coq.proof_file import _AuxFile, ProofFile


def test_set_cache_size():
    _AuxFile.set_cache_size(256)
    _AuxFile._AuxFile__load_library.cache_info().maxsize == 256
    _AuxFile.set_cache_size(512)
    _AuxFile._AuxFile__load_library.cache_info().maxsize == 512
    ProofFile.set_library_cache_size(256)
    _AuxFile._AuxFile__load_library.cache_info().maxsize == 256
