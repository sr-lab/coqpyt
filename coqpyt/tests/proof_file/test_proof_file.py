import pytest

from coqpyt.coq.lsp.structs import *
from coqpyt.coq.exceptions import *
from coqpyt.coq.structs import TermType

from utility import *


class TestProofValidFile(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_valid.v")

    def test_valid_file(self):
        proofs = self.proof_file.proofs
        check_proofs(
            "tests/proof_file/expected/valid_file.yml",
            proofs,
            coq_version=self.coq_version,
        )

    def test_exec(self):
        # Rollback whole file
        self.proof_file.exec(-self.proof_file.steps_taken)
        assert "plus_O_n" in self.proof_file.context.terms
        assert self.proof_file.context.get_term("plus_O_n").module == []
        assert self.proof_file.context.curr_modules == []

        # Check if roll back works for imports
        assert "∀ x .. y , P : type_scope" not in self.proof_file.context.terms
        self.proof_file.exec(1)
        assert "∀ x .. y , P : type_scope" in self.proof_file.context.terms

        steps = self.proof_file.exec(6)
        assert len(steps) == 6
        assert steps[-1].text == "\n      intros n."
        assert self.proof_file.context.curr_modules == ["Out", "In"]
        assert "plus_O_n" in self.proof_file.context.terms
        assert self.proof_file.context.get_term("plus_O_n").module == ["Out", "In"]


class TestProofImports(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_imports/test_import.v", workspace="test_imports/")

    def test_imports(self):
        check_proofs(
            "tests/proof_file/expected/imports.yml",
            self.proof_file.proofs,
            coq_version=self.coq_version,
        )

    def test_exec(self):
        # Rollback whole file
        self.proof_file.exec(-self.proof_file.steps_taken)
        # mult_0_plus is not defined because the import of test_import2 is not executed
        assert "mult_0_plus" not in self.proof_file.context.terms

        self.proof_file.exec(2)
        assert "mult_0_plus" in self.proof_file.context.terms
        # definition of test_import2
        assert (
            self.proof_file.context.get_term("mult_0_plus").text
            == "Definition mult_0_plus : forall n m : nat, 0 + 0 + (S n * m) = S n * m."
        )

        self.proof_file.exec(9)
        assert "mult_0_plus" in self.proof_file.context.terms
        # definition of test_import
        assert (
            self.proof_file.context.get_term("mult_0_plus").text
            == "Definition mult_0_plus : ∀ n m : nat, 0 + (S n * m) = S n * m."
        )


class TestProofNonEndingProof(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_non_ending_proof.v")

    def test_non_ending_proof(self):
        assert len(self.proof_file.open_proofs) == 1
        assert len(self.proof_file.open_proofs[0].steps) == 3


class TestProofExistsNotation(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_exists_notation.v")

    def test_exists_notation(self):
        """Checks if the exists notation is handled. The exists notation is defined
        with 'exists', but the search can be done without the '.
        """
        assert (
            self.proof_file.context.get_notation("exists _ .. _ , _", "type_scope").text
            == "Notation \"'exists' x .. y , p\" := (ex (fun x => .. (ex (fun y => p)) ..)) (at level 200, x binder, right associativity, format \"'[' 'exists' '/ ' x .. y , '/ ' p ']'\") : type_scope."
        )


class TestProofListNotation(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_list_notation.v")

    # FIXME: Refer to issue #24: https://github.com/sr-lab/coqpyt/issues/24
    @pytest.mark.skip(reason="Skipping due to non-deterministic behaviour")
    def test_list_notation(self):
        check_proofs(
            "tests/proof_file/expected/list_notation.yml", self.proof_file.proofs
        )


class TestProofUnknownNotation(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_unknown_notation.v")

    def test_unknown_notation(self):
        """Checks if it is able to handle the notation { _ } that is unknown for the
        Locate command because it is a default notation.
        """
        with pytest.raises(NotationNotFoundException):
            assert self.proof_file.context.get_notation("{ _ }", "")


class TestProofNestedProofs(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_nested_proofs.v")

    def test_nested_proofs(self):
        proof_file = self.proof_file
        proofs = proof_file.proofs
        assert len(proofs) == 2

        steps = ["\n    intros n.", "\n    simpl; reflexivity.", "\n    Qed."]
        assert len(proofs[0].steps) == len(steps)
        for i, step in enumerate(proofs[0].steps):
            assert step.text == steps[i]

        theorem = "Theorem mult_0_plus : forall n m : nat, S n * m = 0 + (S n * m)."
        steps = [
            "\nProof.",
            "\nintros n m.",
            "\n\nrewrite <- (plus_O_n ((S n) * m)).",
            "\nreflexivity.",
            "\nQed.",
        ]
        assert proofs[1].text == theorem
        assert len(proofs[1].steps) == len(steps)
        for i, step in enumerate(proofs[1].steps):
            assert step.text == steps[i]

        proofs = proof_file.open_proofs
        assert len(proofs) == 2

        steps = [
            "\n    intros n.",
            "\n    simpl; reflexivity.",
        ]
        assert len(proofs[0].steps) == 2
        for i, step in enumerate(proofs[0].steps):
            assert step.text == steps[i]

        steps = [
            "\n    intros n.",
            "\n    simpl; reflexivity.",
        ]
        assert len(proofs[1].steps) == 2
        for i, step in enumerate(proofs[1].steps):
            assert step.text == steps[i]


class TestProofTheoremTokens(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_theorem_tokens.v")

    def test_theorem_tokens(self):
        proofs = self.proof_file.proofs
        assert len(proofs) == 7
        assert list(map(lambda proof: proof.type, proofs)) == [
            TermType.REMARK,
            TermType.FACT,
            TermType.COROLLARY,
            TermType.PROPOSITION,
            TermType.PROPERTY,
            TermType.THEOREM,
            TermType.LEMMA,
        ]


class TestProofBullets(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_bullets.v")

    def test_bullets(self):
        proofs = self.proof_file.proofs
        assert len(proofs) == 1
        steps = [
            "\nProof.",
            "\n    intros x y.",
            " split.",
            "\n    -",
            "reflexivity.",
            "\n    -",
            " reflexivity.",
            "\nQed.",
        ]
        assert len(proofs[0].steps) == len(steps)
        for i, step in enumerate(proofs[0].steps):
            assert step.text == steps[i]


class TestProofObligation(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_obligation.v")

    def test_obligation(self):
        # Rollback whole file (except slow import)
        self.proof_file.exec(-self.proof_file.steps_taken + 1)
        proofs = self.proof_file.proofs
        assert len(proofs) == 0
        self.proof_file.run()
        proofs = self.proof_file.proofs
        assert len(proofs) == 13

        statement_context = [
            (
                "Inductive nat : Set := | O : nat | S : nat -> nat.",
                TermType.INDUCTIVE,
                [],
            ),
            ("Notation dec := sumbool_of_bool.", TermType.NOTATION, []),
            (
                "Fixpoint leb n m : bool := match n, m with | 0, _ => true | _, 0 => false | S n', S m' => leb n' m' end.",
                TermType.FIXPOINT,
                [],
            ),
            ("Notation pred := Nat.pred (only parsing).", TermType.NOTATION, []),
            (
                'Notation "{ x : A | P }" := (sig (A:=A) (fun x => P)) : type_scope.',
                TermType.NOTATION,
                [],
            ),
            ('Notation "x = y" := (eq x y) : type_scope.', TermType.NOTATION, []),
        ]
        texts = [
            "Obligation 2 of id2.",
            "Next Obligation of id2.",
            "Obligation 2 of id3 : type with reflexivity.",
            "Next Obligation of id3 with reflexivity.",
            "Next Obligation.",
            "Next Obligation with reflexivity.",
            "Obligation 1.",
            "Obligation 2 : type with reflexivity.",
            "Obligation 1 of id with reflexivity.",
            "Obligation 1 of id : type.",
            "Obligation 2 : type.",
        ]
        programs = [
            ("#[global, program]", "id2", "S (pred n)"),
            ("#[global, program]", "id2", "S (pred n)"),
            ("Local Program", "id3", "S (pred n)"),
            ("Local Program", "id3", "S (pred n)"),
            ("#[local, program]", "id1", "S (pred n)"),
            ("#[local, program]", "id1", "S (pred n)"),
            ("Global Program", "id4", "S (pred n)"),
            ("Global Program", "id4", "S (pred n)"),
            ("#[program]", "id", "pred (S n)"),
            ("Program", "id", "S (pred n)"),
            ("Program", "id", "S (pred n)"),
        ]

        obligations = proofs[:8] + proofs[-3:]
        for i, proof in enumerate(obligations):
            compare_context(statement_context, proof.context)
            assert proof.text == texts[i]
            assert proof.program is not None
            assert (
                proof.program.text
                == programs[i][0]
                + " Definition "
                + programs[i][1]
                + " (n : nat) : { x : nat | x = n } := if dec (Nat.leb n 0) then 0%nat else "
                + programs[i][2]
                + "."
            )
            assert len(proof.steps) == 2
            assert proof.steps[0].text == "\n  dummy_tactic n e."

        statement_context = [
            (
                "Inductive nat : Set := | O : nat | S : nat -> nat.",
                TermType.INDUCTIVE,
                [],
            ),
            ('Notation "x = y" := (eq x y) : type_scope.', TermType.NOTATION, []),
            (
                "Program Definition id (n : nat) : { x : nat | x = n } := if dec (Nat.leb n 0) then 0%nat else S (pred n).",
                TermType.DEFINITION,
                ["Out"],
            ),
        ]
        texts = [
            "Program Lemma id_lemma (n : nat) : id n = n.",
            "Program Theorem id_theorem (n : nat) : id n = n.",
        ]
        for i, proof in enumerate(proofs[8:-3]):
            compare_context(statement_context, proof.context)
            assert proof.text == texts[i]
            assert proof.program is None
            assert len(proof.steps) == 3
            assert proof.steps[1].text == " destruct n; try reflexivity."


class TestProofModuleType(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_module_type.v")

    def test_proof_module_type(self):
        # We ignore proofs inside a Module Type since they can't be used outside
        # and should be overriden.
        assert len(self.proof_file.proofs) == 1


class TestProofTypeClass(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_type_class.v")

    def test_type_class(self):
        proof_file = self.proof_file
        assert len(proof_file.proofs) == 2
        assert len(proof_file.proofs[0].steps) == 4
        assert (
            proof_file.proofs[0].text
            == "#[refine] Global Instance unit_EqDec : TypeClass.EqDecNew unit := { eqb_new x y := true }."
        )

        context = [
            (
                "Class EqDecNew (A : Type) := { eqb_new : A -> A -> bool ; eqb_leibniz_new : forall x y, eqb_new x y = true -> x = y ; eqb_ident_new : forall x, eqb_new x x = true }.",
                TermType.CLASS,
                ["TypeClass"],
            ),
            ("Inductive unit : Set := tt : unit.", TermType.INDUCTIVE, []),
            (
                "Inductive bool : Set := | true : bool | false : bool.",
                TermType.INDUCTIVE,
                [],
            ),
        ]
        compare_context(context, proof_file.proofs[0].context)

        assert (
            proof_file.proofs[1].text
            == "Instance test : TypeClass.EqDecNew unit -> TypeClass.EqDecNew unit."
        )

        context = [
            (
                'Notation "A -> B" := (forall (_ : A), B) : type_scope.',
                TermType.NOTATION,
                [],
            ),
            (
                "Class EqDecNew (A : Type) := { eqb_new : A -> A -> bool ; eqb_leibniz_new : forall x y, eqb_new x y = true -> x = y ; eqb_ident_new : forall x, eqb_new x x = true }.",
                TermType.CLASS,
                ["TypeClass"],
            ),
            ("Inductive unit : Set := tt : unit.", TermType.INDUCTIVE, []),
        ]
        compare_context(context, proof_file.proofs[1].context)


class TestProofGoal(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_goal.v")

    def test_goal(self):
        assert len(self.proof_file.proofs) == 3
        goals = [
            "Definition ignored : forall P Q: Prop, (P -> Q) -> P -> Q.",
            "Goal forall P Q: Prop, (P -> Q) -> P -> Q.",
            "Goal forall P Q: Prop, (P -> Q) -> P -> Q.",
        ]
        for i, proof in enumerate(self.proof_file.proofs):
            assert proof.text == goals[i]
            compare_context(
                [
                    (
                        'Notation "A -> B" := (forall (_ : A), B) : type_scope.',
                        TermType.NOTATION,
                        [],
                    )
                ],
                proof.context,
            )


class TestProofCmd(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_proof_cmd.v")

    def test_proof_cmd(self):
        assert len(self.proof_file.proofs) == 3
        goals = [
            "Goal ∃ (m : nat), S m = n.",
            "Goal ∃ (m : nat), S m = n.",
            "Goal nat.",
        ]
        proofs = [
            "\n  Proof using Hn.",
            "\n  Proof with auto.",
            "\n  Proof 0.",
        ]
        for i, proof in enumerate(self.proof_file.proofs):
            assert proof.text == goals[i]
            assert proof.steps[0].text == proofs[i]


class TestProofSection(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_section_terms.v")

    def test_section(self):
        assert len(self.proof_file.proofs) == 1
        assert self.proof_file.proofs[0].text == "Let ignored : nat."
        assert len(self.proof_file.context.local_terms) == 0


class TestModuleInline(SetupProofFile):
    def setup_method(self, method):
        self.setup("test_module_inline.v")

    def test_module_import(self):
        self.proof_file.exec(-self.proof_file.steps_taken)
        self.proof_file.run()
        assert self.proof_file.context.curr_modules == []
        assert not self.proof_file.context.in_module_type
