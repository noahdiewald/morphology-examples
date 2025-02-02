(* This is taken from Needle's THS, which doesn't compile at the moment. *)

Section Primitives.
    Axiom e prop : Set.
    Axiom truth falsity : prop.
    Axiom p_not : prop -> prop.
    Axiom p_and p_or p_implies p_iff : prop -> prop -> prop.
    Axiom p_entails : prop -> prop -> Prop.
    Definition p_equiv : prop -> prop -> Prop := fun p q : prop => (p_entails p q) /\ (p_entails q p).
End Primitives.

(* Basics of stat_term *)
Section Static_Types.
    Inductive stat_term : Set := ent : stat_term | prp : stat_term | func : stat_term -> stat_term -> stat_term.

    Fixpoint Sns (s : stat_term) : Set
        :=  match s with
                | ent       => e
                | prp       => prop
                | func a b  => (Sns a) -> (Sns b)
            end.

    Fixpoint Ext (s : stat_term) : Set
        :=  match s with
                | ent       => e
                | prp       => bool
                | func a b  => (Sns a) -> (Ext b)
            end.
End Static_Types.

(* adding terms for propositional quantifiers, equality *)
Section Eq_Quant.
    Axiom p_forall p_exists : forall s : stat_term, (Sns s -> prop) -> prop.
    Axiom p_equals : forall s : stat_term, Sns s -> Sns s -> prop.
End Eq_Quant.

(* Notations for prop operators *)
Module Sem_notations.
    (* Adding a new "sem_scope" for these notations- should allow us to use "not" w/o naming conflicts *)
    Declare Scope sem_scope. (* todo: add "Declare" to list of keywords for syntax highlighting *)
    Infix "entails"     := p_entails        (at level 50, no associativity) : sem_scope.
    Infix "≡"           := p_equiv          (at level 40, no associativity) : sem_scope.
    Infix "and"         := p_and            (at level 80)   : sem_scope.
    Infix "or"          := p_or             (at level 80)   : sem_scope.
    Infix "implies"     := p_implies        (at level 80)   : sem_scope.
    Infix "iff"         := p_iff            (at level 80)   : sem_scope.
    Infix "equals"      := (p_equals _)     (at level 80)   : sem_scope. (* we'll see if this works... *)
    Notation "'not' p"  := (p_not p)        (at level 80)   : sem_scope. (* I could've just named p_not as not, apparently *)
    Open Scope sem_scope.
End Sem_notations.
Import Sem_notations.

(* Definitions and assumptions pertaining to the definition of world/establishing them as ultrafilters over prop *)
Section Ultra.
    Definition pset : Set := prop -> bool.

    Definition uc  : pset -> Prop := fun s : pset => forall p q : prop,  (s p) = true  -> p entails q -> (s q) = true.
    Definition ac  : pset -> Prop := fun s : pset => forall p q : prop,  (s p) = true  -> (s q) = true -> (s (p and q)) = true.
    Definition sai : pset -> Prop := fun s : pset => forall p   : prop, ((s p) = true) \/ ((s (not p)) = true).
    Definition cst : pset -> Prop := fun s : pset => (s falsity) = false.
    Definition ultrafilter : pset -> Prop := fun s : pset => (uc s) /\ (ac s) /\ (sai s) /\ (cst s).

    Definition world    : Set := {s : pset | ultrafilter s}.
    Definition facts    : world -> pset := fun w : world => proj1_sig w.
    Definition tv       : prop -> world -> bool := fun (p : prop) (w : world) => facts w p.

    (* projection functions for the subproofs of a world being an ultrafilter *)
    Definition upcl     : forall w : world, uc  (facts w)
        := sig_ind (fun w : world => uc  (proj1_sig w)) (fun (s : pset) (u : ultrafilter s) => proj1 u).
    Definition ancl     : forall w : world, ac  (facts w)
        := sig_ind (fun w : world => ac  (proj1_sig w)) (fun (s : pset) (u : ultrafilter s) => proj1 (proj2 u)).
    Definition stalis   : forall w : world, sai (facts w)
        := sig_ind (fun w : world => sai (proj1_sig w)) (fun (s : pset) (u : ultrafilter s) => proj1 (proj2 (proj2 u))).
    Definition consist  : forall w : world, cst (facts w)
        := sig_ind (fun w : world => cst (proj1_sig w)) (fun (s : pset) (u : ultrafilter s) => proj2 (proj2 (proj2 u))).

    (* in effect, this axiom asserts proof irrelevance for the proofs of ultrafilterhood *)
    Axiom facts_inj  : forall w v : world, (facts w) = (facts v) -> w = v.
    Definition facts_onto : forall s : pset, ultrafilter s -> exists w : world, s = (facts w)
        := fun (s : pset) (u : ultrafilter s) => ex_intro (fun w : world => s = facts w) (exist ultrafilter s u) eq_refl.
End Ultra.

(* general ext_at function *)
Fixpoint ext_at (s : stat_term) : Sns s -> world -> Ext s
    :=  match s with
            | ent       =>  fun (x : e) (w : world) => x
            | prp       =>  tv
            | func a b  =>  fun (f : Sns a -> Sns b) (w : world) (x : Sns a) => ext_at b (f x) w
        end.

(* axiomatization of entails *)
Section Entails.
    (* "entails" is a preorder *)
    Axiom entails_refl : forall p : prop, p entails p.
    Axiom entails_trans: forall p q r : prop, p entails q -> q entails r -> p entails r.

    (* "and" is a glb *)
    Axiom p_and_e1  : forall p q : prop, (p and q) entails p.
    Axiom p_and_e2  : forall p q : prop, (p and q) entails q.
    Axiom p_and_i   : forall p q r : prop, p entails q -> p entails r -> p entails (q and r).

    (* "or" is an lub *)
    Axiom p_or_e    : forall p q r : prop, p entails r -> q entails r -> (p or q) entails r.
    Axiom p_or_i1   : forall p q : prop, p entails (p or q).
    Axiom p_or_i2   : forall p q : prop, q entails (p or q).

    (* "truth" and "falsity" are top and bottom, respectively *)
    Axiom truth_top     : forall p : prop, p entails truth.
    Axiom falsity_bot   : forall p : prop, falsity entails p.

    (* "implies" is a residual operator *)
    Axiom residual_law1 : forall p q r : prop, (p and q) entails r -> p entails (q implies r).
    Axiom residual_law2 : forall p q r : prop, p entails (q implies r) -> (p and q) entails r.

    (* "iff" is bi-implication *)
    Axiom p_iff_e1  : forall p q : prop, (p iff q) entails (p implies q).
    Axiom p_iff_e2  : forall p q : prop, (p iff q) entails (q implies p).
    Axiom p_iff_i   : forall p q : prop, ((p implies q) and (q implies p)) entails (p iff q).

    (* "not" is complement, also classicality *)
    Axiom p_not_comp    : forall p : prop, (p and (not p)) entails falsity.
    Axiom pif_p_not_p   : forall p : prop, (p implies falsity) entails (not p).
    Axiom dne           : forall p : prop, (not (not p)) entails p.

    (* axioms for the quantifiers *)
    Axiom p_forall_e    : forall (s : stat_term) (R : Sns s -> prop) (x : Sns s), (p_forall s R) entails (R x).
    Axiom p_forall_i    : forall (s : stat_term) (R : Sns s -> prop) (p : prop), (forall x : Sns s, p entails (R x)) -> p entails (p_forall s R).
    Axiom p_exists_e    : forall (s : stat_term) (R : Sns s -> prop) (p : prop), (forall x : Sns s, (R x) entails p) -> (p_exists s R) entails p.
    Axiom p_exists_i    : forall (s : stat_term) (R : Sns s -> prop) (x : Sns s), (R x) entails (p_exists s R).

    (* non-degeneracy *)
    Axiom nondeg        : ~(truth entails falsity).

    (* equality axioms *)
    Axiom eq_one    : forall (s : stat_term) (x y : Sns s), (truth entails (x equals y)) \/ ((x equals y) entails falsity). (* originally ≡, but proofs of x=y⇒truth and falsity⇒x=y are trivial *)
    Axiom eq_two    : forall (s : stat_term) (x y : Sns s), (truth entails (x equals y)) <-> (x = y).
End Entails.
