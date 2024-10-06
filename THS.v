(*  Dubbing this form of the static semantics THS- Tractarian Hyperintensional Semantics
    The idea here is to eschew the agnosticism of AHS and embrace the tractarian approach to relating (static, linguistic) propositions and worlds
    by identifying worlds with ultrafilters on propositions, treating propositional entailment as a primitive relation which is axiomatized as a pre-boolean algebra. *)

(* Missing two quantifier proofs *)
(* check for other pre-boolean stuff to prove? *)

(* todo's from Carl:
    1. replace facts_inj, make world its own primitive type which maps to {f : pset | ultrafilter f}, quotient relation to make proof irrelevance fall out
    2. maybe try a version with the hyperintensional type i for individual concepts, with extension type e *)


(* Assumptions for the signature of the theory *)
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

Infix "→i" := implb (at level 50, no associativity) : bool_scope.
Notation "¬i x" := (negb x) (at level 50 ,no associativity) : bool_scope.
Open Scope bool_scope.

(* lemmas for proving facts about entails *)
Section bool_lemmas.
    Definition demorgish : forall s t : bool, ~((s = true) /\ (t = true)) -> ((s = false) \/ (t = false))
        :=  fun s : bool => bool_ind
                (fun t : bool => ~((s = true) /\ (t = true)) -> ((s = false) \/ (t = false)))
                (fun n : ~((s = true) /\ (true = true)) => or_introl
                    (bool_ind (fun b : bool => ~((b = true) /\ (true = true)) -> (b = false))
                        (fun m : ~((true = true) /\ (true = true)) => False_ind (true = false) (m (conj eq_refl eq_refl)))
                        (fun _  => eq_refl) s n))
                (fun _ => or_intror eq_refl).

    Definition sflortfltosntfl : forall s t : bool, ((s = false) \/ (t = false)) -> ((s && t) = false)
        := fun s t : bool => or_ind (fun a : s = false => f_equal (fun c : bool => c && t) a)
                                    (fun b : t = false => bool_ind (fun c : bool => (c && t) = false) b eq_refl s).

    Definition tnf : true <> false := eq_ind true (fun c : bool => if c then True else False) I false.

    Definition sorttrtostrorttr : forall s t : bool, (s || t) = true -> ((s = true) \/ (t = true))
        := fun s t : bool => bool_ind   (fun b : bool => (b || t) = true -> (b = true) \/ (t = true))
                                        (fun e : true = true => or_introl e)
                                        (fun e : t = true => or_intror e) s.

    Definition nttof : forall s : bool, s <> true -> s = false
        := bool_ind (fun s : bool => (s <> true) -> s = false)
                    (fun n : true <> true => False_ind (true = false) (n eq_refl))
                    (fun _ : false <> true => eq_refl).

    Definition bnttont : forall s : bool, s <> true -> ¬is = true
        := bool_ind (fun s : bool => (s <> true) -> (¬is = true))
                    (fun n : true <> true => False_ind (false = true) (n eq_refl))
                    (fun _ : false <> true => eq_refl).

    Definition nftot : forall s : bool, s <> false -> s = true
        := bool_ind (fun s : bool => s <> false -> s = true) (fun _ => eq_refl)
            (fun n : false <> false => False_ind (false = true) (n eq_refl)).

    Definition randbool : forall b c : bool, ¬ib = c -> b = ¬ic
        := fun b c : bool => bool_ind (fun s : bool => ¬is = c -> s = ¬ic)
                                (fun e : false = c => f_equal negb e) (fun e : true = c => f_equal negb e) b.

    Definition dubneg : forall b : bool, b = ¬i(¬ib) := bool_ind (fun b : bool => b = ¬i(¬ib)) eq_refl eq_refl.

    Definition sflottr2sittr : forall s t : bool, (¬is = true) \/ (t = true) -> (s→it) = true
        :=  fun s t : bool =>
            or_ind  (fun c : ¬is = true => f_equal (fun b : bool => b→it) (eq_trans (dubneg s) (f_equal negb c)))
                    (fun d :  t = true => eq_trans (f_equal (implb s) d)
                        (bool_ind (fun b : bool => (b→itrue) = true) eq_refl eq_refl s)).

    Definition stratfl2sotfl : forall s t : bool, (s = true) -> (t = false) -> (s→it) = false
        := fun (s t : bool) (c : s = true) (d : t = false) => f_equal2 implb c d.
End bool_lemmas.

(* lemmas about prop for proving theorems, also includes p_not_ax though *)
Section prop_lemmas.
    Definition pandcomm : forall p q : prop, (p and q) entails (q and p)
        := fun p q : prop => p_and_i (p and q) q p (p_and_e2 p q) (p_and_e1 p q).

    Definition propdist1a : forall p q r : prop, (p and (q or r)) entails ((p and q) or (p and r))
        := fun p q r : prop =>
            entails_trans (p and (q or r)) ((q or r) and p) ((p and q) or (p and r))
            (pandcomm p (q or r))
            (residual_law2 (q or r) p ((p and q) or (p and r))
                (p_or_e q r (p implies ((p and q) or (p and r)))
                    (residual_law1 q p ((p and q) or (p and r))
                        (entails_trans (q and p) (p and q) ((p and q) or (p and r)) (pandcomm q p) (p_or_i1 (p and q) (p and r))))
                    (residual_law1 r p ((p and q) or (p and r))
                        (entails_trans (r and p) (p and r) ((p and q) or (p and r)) (pandcomm r p) (p_or_i2 (p and q) (p and r)))))).

    Definition propdemo : forall p q : prop, ((not p) and (not q)) entails (not (p or q))
        := fun p q : prop =>
            entails_trans ((not p) and (not q)) ((p or q) implies falsity) (not (p or q))
                (residual_law1 ((not p) and (not q)) (p or q) falsity
                    (entails_trans (((not p) and (not q)) and (p or q))
                        ((((not p) and (not q)) and p) or (((not p) and (not q)) and q))
                        falsity (propdist1a ((not p) and (not q)) p q)
                        (p_or_e (((not p) and (not q)) and p) (((not p) and (not q)) and q) falsity
                           (entails_trans (((not p) and (not q)) and p) (p and (not p)) falsity
                                (p_and_i (((not p) and (not q)) and p) p (not p)
                                    (p_and_e2 ((not p) and (not q)) p)
                                    (entails_trans (((not p) and (not q)) and p) ((not p) and (not q)) (not p)
                                        (p_and_e1 ((not p) and (not q)) p)
                                        (p_and_e1 (not p) (not q))))
                                (p_not_comp p))
                            (entails_trans (((not p) and (not q)) and q) (q and (not q)) falsity
                                (p_and_i (((not p) and (not q)) and q) q (not q)
                                    (p_and_e2 ((not p) and (not q)) q)
                                    (entails_trans (((not p) and (not q)) and q) ((not p) and (not q)) (not q)
                                        (p_and_e1 ((not p) and (not q)) q)
                                        (p_and_e2 (not p) (not q))))
                                (p_not_comp q)))))
                (pif_p_not_p (p or q)).

    Definition disjcs : forall (p q : prop) (w : world), (tv (p or q) w) = false -> ((tv p w) = false) /\ ((tv q w) = false)
        := fun (p q : prop) (w : world) (e : (tv (p or q) w) = false) =>
            conj    (nttof (tv p w) (fun c : (tv p w) = true => tnf (eq_trans (eq_sym (upcl w p (p or q) c (p_or_i1 p q))) e)))
                    (nttof (tv q w) (fun c : (tv q w) = true => tnf (eq_trans (eq_sym (upcl w q (p or q) c (p_or_i2 p q))) e))).

    (* should be in prop_thms, but mvngout depends on it *)
    Definition p_not_ax      : forall (p : prop) (w : world), (tv (not p) w) = ¬i(tv p w)
        :=  fun (p : prop) (w : world) => or_ind
                (fun e : (tv p w) = true =>
                   eq_ind true (fun b : bool => (tv (not p) w) = ¬ib)
                      (nttof (tv (not p) w)
                         (fun d : (tv (not p) w) = true =>
                            tnf (eq_trans   (eq_sym (upcl w (p and (not p)) falsity (ancl w p (not p) e d) (p_not_comp p)))
                                            (consist w))))
                      (tv p w) (eq_sym e))
                (fun e : (tv (not p) w) = true =>
                   eq_ind true (fun b : bool => b = ¬i(tv p w))
                      (eq_sym (bnttont (tv p w)
                            (fun d : (tv p w) = true =>
                                tnf (eq_trans   (eq_sym (upcl w (p and (not p)) falsity (ancl w p (not p) d e) (p_not_comp p)))
                                                (consist w)))))
                      (tv (not p) w) (eq_sym e))
                (stalis w p).

    Definition mvngout : forall (p : prop) (w : world) (b : bool), (tv p w) = b -> (tv (not p) w) = ¬ib
        := fun (p : prop) (w : world) (b : bool) (e : (tv p w) = b) => eq_trans (p_not_ax p w) (f_equal negb e).

    Definition pimplies_true : forall (p q : prop) (w : world), (tv (p implies q) w) = true -> ((tv p w) →i (tv q w)) = true
        :=  fun (p q : prop) (w : world) (e : (tv (p implies q) w) = true) =>
            sflottr2sittr (tv p w) (tv q w)
                (or_ind (fun x : (tv (not p) w) = true => or_introl (eq_trans (eq_sym (p_not_ax p w)) x))
                        (fun y : (tv q w) = true => or_intror y)
                        (bool_ind
                            (fun b : bool => (tv q w) = b -> ((tv (not p) w) = true) \/ ((tv q w) = true))
                            (fun c : (tv q w) = true => or_intror c)
                            (fun d : (tv q w) = false =>
                                or_introl (or_ind
                                    (fun m : (tv p w) = true =>
                                        False_ind ((tv (not p) w) = true)
                                            (tnf (eq_trans (eq_sym (upcl w ((p implies q) and p) q
                                                                            (ancl w (p implies q) p e m)
                                                                            (residual_law2 (p implies q) p q
                                                                            (entails_refl (p implies q))))) d)))
                                      (fun n : (tv (not p) w) = true => n)
                                      (stalis w p)))
                            (tv q w) eq_refl)).

    Definition pimplies_false : forall (p q : prop) (w : world), (tv (p implies q) w) = false -> ((tv p w) →i (tv q w)) = false
        :=  fun (p q : prop) (w : world) (e : (tv (p implies q) w) = false) =>
            stratfl2sotfl (tv p w) (tv q w)
                (nftot (tv p w)
                     (fun c : (tv p w) = false =>
                        tnf (eq_trans
                                (eq_sym (upcl w (not p) (p implies q) (mvngout p w false c)
                                    (residual_law1 (not p) p q
                                        (entails_trans ((not p) and p) (p and (not p)) q
                                            (pandcomm (not p) p)
                                            (entails_trans (p and (not p)) falsity q (p_not_comp p) (falsity_bot q))))))
                                e)))
                (nttof (tv q w)
                     (fun d : (tv q w) = true =>
                        tnf (eq_trans (eq_sym (upcl w q (p implies q) d (residual_law1 q p q (p_and_e1 q p)))) e))).
End prop_lemmas.

Section prop_thms.
    Definition p_and_ax      : forall (p q : prop) (w : world), (tv (p and q) w) = ((tv p w) && (tv q w))
        := fun (p q : prop) (w : world) =>
            eq_sym (bool_ind (fun b : bool => ((tv (p and q) w) = b) -> (((tv p w) && (tv q w)) = b))
                            (fun e : tv (p and q) w = true => f_equal2 andb (upcl w (p and q) p e (p_and_e1 p q))
                                                                            (upcl w (p and q) q e (p_and_e2 p q)))
                            (fun e : tv (p and q) w = false => sflortfltosntfl (tv p w) (tv q w) (demorgish (tv p w) (tv q w)
                                (and_ind (fun (a : (tv p w) = true) (b : (tv q w) = true) =>
                                    tnf (eq_trans (eq_sym (ancl w p q a b)) e)))))
                            (tv (p and q) w) eq_refl).

    Definition p_or_ax       : forall (p q : prop) (w : world), (tv (p or q) w) = ((tv p w) || (tv q w))
        := fun (p q : prop) (w : world) =>
            eq_sym (bool_ind (fun b : bool => (tv (p or q) w) = b -> ((tv p w) || (tv q w)) = b)
                    (fun e : (tv (p or q) w) = true =>
                        bool_ind (fun b : bool => (tv p w) = b -> (b || (tv q w)) = true) (fun _ => eq_refl)
                            (fun c : (tv p w) = false =>
                                nftot (tv q w)
                                    (fun d : (tv q w) = false =>
                                        tnf (eq_trans (eq_sym e)
                                                (randbool (tv (p or q) w) true
                                                    (eq_trans (eq_sym (p_not_ax (p or q) w))
                                                        (upcl w ((p_not p) and (p_not q)) (p_not (p or q))
                                                            (ancl w (p_not p) (p_not q) (mvngout p w false c) (mvngout q w false d))
                                                            (propdemo p q)))))))
                            (tv p w)
                            eq_refl)
                    (fun e : (tv (p or q) w) = false => and_ind (fun a b => f_equal2 orb a b) (disjcs p q w e))
                    (tv (p or q) w)
                    eq_refl).

    Definition p_implies_ax  : forall (p q : prop) (w : world), (tv (p implies q) w) = ((tv p w) →i  (tv q w))
        := fun (p q : prop) (w : world) => eq_sym (bool_ind (fun b : bool => (tv (p implies q) w) = b -> ((tv p w) →i (tv q w)) = b)
        (pimplies_true p q w) (pimplies_false p q w) (tv (p implies q) w) eq_refl).

    Definition truth_ax      : forall w : world, (tv truth w) = true
        := fun w : world =>
            or_ind  (fun e : (tv truth w) = true => e)
                    (fun e : (tv (not truth) w) = true =>
                       False_ind ((tv truth w) = true)
                         (tnf   (eq_trans
                                    (eq_sym (upcl w (not truth) falsity e
                                         (entails_trans (not truth) (truth and (not truth)) falsity
                                            (p_and_i (not truth) truth (not truth)
                                                (truth_top (not truth)) (entails_refl (not truth)))
                                            (p_not_comp truth))))
                                    (consist w))))
                    (stalis w truth).

    Definition falsity_ax    : forall w : world, (tv falsity w) = false := consist.

    Definition p_iff_ax      : forall (p q : prop) (w : world), (tv (p iff q) w) = ((tv (p implies q) w) && (tv (q implies p) w))
        := fun (p q : prop) (w : world) => eq_sym
          (let piq := p implies q in
           let qip := q implies p in
           bool_ind (fun b : bool => tv (p iff q) w = b -> tv piq w && tv qip w = b)
             (fun e : tv (p iff q) w = true =>
              f_equal2 andb (upcl w (p iff q) piq e (p_iff_e1 p q))
                (upcl w (p iff q) qip e (p_iff_e2 p q)))
             (fun e : tv (p iff q) w = false =>
              sflortfltosntfl (tv piq w) (tv qip w)
                (demorgish (tv piq w) (tv qip w)
                   (fun H : tv piq w = true /\ tv qip w = true =>
                    match H with
                    | conj a b =>
                        tnf
                          (eq_trans
                             (eq_sym
                                (upcl w (piq and qip) (p iff q)
                                   (ancl w piq qip a b) (p_iff_i p q))) e)
                    end))) (tv (p iff q) w) eq_refl).

    Definition p_equals_ax   : forall (s : stat_term) (x y : Sns s) (w : world), ((tv (x equals y) w) = true) <-> (x = y)
        :=  fun (s : stat_term) (x y : Sns s) (w : world) =>
            conj    (fun e : (tv (x equals y) w) = true =>
                        proj1 (eq_two s x y)
                            (or_ind (fun c : truth entails (x equals y) => c)
                                    (fun d : (x equals y) entails falsity => False_ind (truth entails (x equals y)) (tnf (eq_trans (eq_sym (upcl w (x equals y) falsity e d)) (consist w))))
                                    (eq_one s x y)))
                    (fun e : x = y => upcl w truth (x equals y) (truth_ax w) (proj2 (eq_two s x y) e)).

    Definition complement   : forall (p : prop) (w : world), (tv (p and (not p)) w) = false
        := fun (p : prop) (w : world) =>
            nttof   (tv (p and (not p)) w)
                    (fun e : tv (p and (not p)) w = true =>
                        tnf (eq_trans (eq_sym (upcl w (p and (not p)) falsity e (p_not_comp p))) (consist w))).

    Definition lem          : forall (p : prop) (w : world), (tv (p or (not p)) w) = true
        :=  fun (p : prop) (w : world) =>
            or_ind  (fun e : (tv p w) = true => upcl w p (p or (not p)) e (p_or_i1 p (not p)))
                    (fun e : (tv (not p) w) = true => upcl w (not p) (p or (not p)) e (p_or_i2 p (not p)))
                    (stalis w p).

    (* (in)equality at one world means (in)equality in all worlds *)
    Definition eqiseqev     : forall (s : stat_term) (x y : Sns s) (w : world), (tv (x equals y) w) = true -> forall u : world, (tv (x equals y) u) = true
        := fun (s : stat_term) (x y : Sns s) (w : world) (e : (tv (x equals y) w) = true) (u : world) => proj2 (p_equals_ax s x y u) (proj1 (p_equals_ax s x y w) e).

    Definition neqisneqev   : forall (s : stat_term) (x y : Sns s) (w : world), (tv (x equals y) w) = false -> forall v : world, (tv (x equals y) v) <> true
        :=  fun (s : stat_term) (x y : Sns s) (w : world) (e : (tv (x equals y) w) = false) (v : world) (c : (tv (x equals y) v) = true) =>
            tnf (eq_trans (eq_sym (eqiseqev s x y v c w)) e).

    Definition pexax_onlyifdir : forall (s : stat_term) (R : Sns s -> prop) (w : world), (exists x : Sns s, (tv (R x) w) = true) -> ((tv (p_exists s R) w) = true)
        := fun (s : stat_term) (R : Sns s -> prop) (w : world) => ex_ind (fun (x : Sns s) (e : tv (R x) w = true) => upcl w (R x) (p_exists s R) e (p_exists_i s R x)).

    Definition pfaax_ifdir  : forall (s : stat_term) (R : Sns s -> prop) (w : world), ((tv (p_forall s R) w) = true) -> (forall x : Sns s, (tv (R x) w) = true)
        := fun (s : stat_term) (R : Sns s -> prop) (w : world) (e : (tv (p_forall s R) w) = true) (x : Sns s) => upcl w (p_forall s R) (R x) e (p_forall_e s R x).

(* had trouble with these apparently *)
    (* Definition p_exists_ax   : forall (R : prop -> prop) (w : world),
                                ((tv (p_exists R) w) = true) <-> (exists p : prop, (tv (R p) w) = true). *)
    (* Definition p_forall_ax   : forall (R : prop -> prop) (w : world),
                                ((tv (p_forall R) w) = true) <-> (forall p : prop, (tv (R p) w) = true). *)
    (* might have to assume this one- can't say w/o proof irrelevance that all proofs that s is an ultrafilter are equal
        (and in fact may not be, without assuming proof irrelevance) *)
    (* not gonna happen w/o proof irrelevance *)
    (* Definition fact_inj : forall w v : world, (facts w) = (facts v) -> w = v. *)
End prop_thms.

(* A place to put any non-logical constants I'll be assuming for examples (eg donkey sentences, consistency, etc) *)
Section non_log.
    Axiom john bill mary : e.
    Axiom rain : prop.
    Axiom donkey bray farmer nonhuman : e -> prop.
    Axiom own beat : e -> e -> prop.
End non_log.


(* idk how to prove these, or even what to assume to get there *)
(* Definition pexax_ifdir : forall (s : stat_term) (R : Sns s -> prop) (w : world), (tv (p_exists s R) w) = true -> exists x : Sns s, (tv (R x) w) = true. *)
(* Definition pfaax_onlyifdir : forall (s : stat_term) (R : Sns s -> prop) (w : world), (forall x : Sns s, (tv (R x) w) = true) -> (tv (p_forall s R) w) = true. *)

Definition pex   : Prop := forall (s : stat_term) (R : Sns s -> prop) (w : world), (tv (p_exists s R) w) = true -> exists x : Sns s, (tv (R x) w) = true.
Definition pfa   : Prop := forall (s : stat_term) (R : Sns s -> prop) (w : world), (forall x : Sns s, (tv (R x) w) = true) -> (tv (p_forall s R) w) = true.
Definition pexdn : Prop := forall (s : stat_term) (R : Sns s -> prop) (w : world), (tv (p_exists s R) w) = true -> ~forall x : Sns s, (tv (R x) w) = false.

(* pexdn -> pfa is provable, but damn it was too friggin long for me to bother with! *)

(* can ignore below this *)

(* Axiom p_forall_i    : forall (s : stat_term) (R : Sns s -> prop) (p : prop), (forall x : Sns s, p entails (R x)) -> p entails (p_forall s R). *)
(* Axiom p_forall_e    : forall (s : stat_term) (R : Sns s -> prop) (x : Sns s), (p_forall s R) entails (R x). *)

(* using upper closure of w *)
(* s : stat_term
R : Sns s -> prop
w : world
f : forall x : Sns s, (tv (R x) w) = true
x : Sns s
============================
truth entails (R x)
(f x) : (facts w (R x)) = true *)


(* using (stalis w) to try to create a contradiction *)
(* s : stat_term
R : Sns s -> prop
w : world
f : forall x : Sns s, (tv (R x) w) = true
n : (tv (not (p_forall s R)) w) = true
============================
False


(randbool (tv (p_forall s R) w) true (eq_trans (eq_sym (p_not_ax (p_forall s R) w)) n)) : (tv (p_forall s R) w) = false *)

(* static generalized quantifiers *)
Definition every : forall s : stat_term, (Sns s -> prop) -> (Sns s -> prop) -> prop
    := fun (s : stat_term) (P Q : Sns s -> prop) => p_forall s (fun x : Sns s => (P x) implies (Q x)).
Definition some  : forall s : stat_term, (Sns s -> prop) -> (Sns s -> prop) -> prop
    := fun (s : stat_term) (P Q : Sns s -> prop) => p_exists s (fun x : Sns s => (P x) and (Q x)).


