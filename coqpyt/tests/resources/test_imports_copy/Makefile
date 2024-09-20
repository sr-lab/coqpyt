# Default target
all: Makefile.coq
	+@$(MAKE) -f Makefile.coq all
.PHONY: all

# Permit local customization
-include Makefile.local

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	@#echo "Forwarding $@"
	+@$(MAKE) -f Makefile.coq $@
phony: ;
.PHONY: phony

clean: Makefile.coq
	+@$(MAKE) -f Makefile.coq clean
	@# Make sure not to enter the `_opam` folder.
	rm .*.aux Makefile.*
.PHONY: clean

# Create Coq Makefile.
Makefile.coq: _CoqProject Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o Makefile.coq $(EXTRA_COQFILES)

# Some files that do *not* need to be forwarded to Makefile.coq.
# ("::" lets Makefile.local overwrite this.)
Makefile Makefile.local _CoqProject $(OPAMFILES):: ;