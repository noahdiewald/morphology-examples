Require Import Coq.Unicode.Utf8.
Load THS.
Load Vect.
Declare Scope dyn_scope.
Open Scope dyn_scope.

Notation "'ₑ.' n" := (Vect e n) (at level 0) : vect_scope.

Definition con : nat → Set :=
  λ n, ₑ.n → prop.

Definition kon : nat → Type :=
  λ i, ∀ n, con n → con (n+i) → Prop.

Fixpoint ᵛe {n} : con n -> prop :=
            match n as k return (con k -> prop) with
            | 0     =>  λ c, c []
            | S i   =>  λ c, p_exists ent (λ x, ᵛe (λ v : ₑ.i, c (x::v)))
            end.

Definition cc : ∀ {i}, kon i → kon i :=
  λ i k n c d, ∃ d', (k n c d') ∧ d = λ v : ₑ.(n + i), c (take n v) and d' v.

Definition NOT : ∀ {i}, kon i → kon 0 :=
  λ i k n c d,
  ∃ d', (k n c d') ∧
        d = λ v : ₑ.(n + 0), not (ᵛe (λ u : ₑ.i, d' ((take n v) ++ u))).

Definition d_AND : ∀ {i j}, kon i → kon j → kon (i + j) :=
  λ {i j} h k n c d,
  ∃ d', (h n c d') ∧ k (n + i) (λ u : ₑ.(n + i), c (take n u) and d' u)
                       (λ v : ₑ.(n + i + j), d (vcast v (add_assoc n i j))).

Infix "AND" := d_AND (at level 20) : dyn_scope.

Definition d_OR : ∀ {i j}, kon i → kon j → kon 0 :=
  λ {i j} h k, NOT ((NOT h) AND (NOT k)).

Infix "OR" := d_OR (at level 20) : dyn_scope.

Definition d_IMPLIES : ∀ {i j}, kon i → kon j → kon 0 :=
  λ {i j} h k, (NOT h) OR (h AND k).

Infix "IMPLIES" := d_IMPLIES (at level 20) : dyn_scope.

Definition pᵢ : nat → Type :=
  λ n, prd n e prop.

Definition dy : nat → nat → Type :=
  λ m n, prd n nat (kon m).

Definition udyn : ∀ i, pᵢ i → Vect nat i → kon 0 :=
  λ i P u n _ d,
  ∃ q : (vmax u) < n, d = λ v : ₑ.(n + 0),
  vuncur i e prop P (imap u (take n v) q).

Definition dyn : ∀ i, pᵢ i → dy 0 i :=
  λ i P, vcur i nat (kon 0) (udyn i P).

Definition d_THAT : ∀ {i j}, dy i 1 → dy j 1 → dy (i + j) 1 :=
  λ {i j} D E n, (D n) AND (E n).
Infix "THAT" := d_THAT (at level 20) : dyn_scope.

Definition cext : ∀ i n : nat, con n → con (n + i) :=
  λ i n c v, c (take n v).

Notation "c ⁺" := (cext 1 _ c) (at level 0) : dyn_scope.

Section ent_cons.
  Definition cent : ∀ {n}, con n → ∀ m, pᵢ 1 → Prop :=
    λ {n} c m P, ∃ q : m < n, ∀ v : ₑ.n, (c v) entails (P (jth e n v m q)).

  Definition ccons : ∀ {n}, con n → ∀ m, pᵢ 1 → Prop :=
    λ {n} c m P,
    ∃ q : m < n, ∀ v : ₑ.n, ~((c v) entails (not (P (jth e n v m q)))).
End ent_cons.

Section Example_Contents.
  Definition theresa : pᵢ 1 → kon 1 :=
    λ P n _ d, d = λ v : ₑ.(n + 1), P (last (vcast v (Sdistr n 0))).

  Definition itsa : pᵢ 1 → kon 0 :=
    λ P n c d,
    ∃ m (q : m < n), (ccons c m nonhuman) ∧ d = λ v : ₑ.(n + 0),
    P (jth e n (take n v) m q).
End Example_Contents.

Definition EXISTS : ∀ {i}, dy i 1 → kon (1 + i) :=
  λ {i} D n c d,
  D n (n + 1) (c)⁺
    (λ v : ₑ.((n + 1) + i),
           d ((take n (take (n + 1) v))
                ++ (drop n (take (n + 1) v)) ++ (drop (n + 1) v))).

Definition FORALL : ∀ {i}, dy i 1 → kon 0 :=
  λ {i} D, NOT (EXISTS (λ j, NOT (D j))).

Definition SOME : ∀ {i j}, dy i 1 → dy j 1 → kon (1 + (i + j)) :=
  λ {i j} D E, EXISTS (D THAT E).

Definition EVERY : ∀ {i j}, dy i 1 → dy j 1 → kon 0 :=
  λ {i j} D E, FORALL (λ n, (D n) IMPLIES (E n)).

Definition IT : nat → ∀ {i}, dy i 1 → kon i :=
  λ n {i} D, D n.

Section Dyn_ana.
    Definition BEAT : dy 0 2 := dyn 2 beat.
    Definition BRAY : dy 0 1 := dyn 1 bray.
    Definition DONKEY  : dy 0 1 := dyn 1 donkey.
    Definition FARMER : dy 0 1 := dyn 1 farmer.
    Definition OWN : dy 0 2 := dyn 2 own.
    Definition RAIN : dy 0 0 := dyn 0 rain.
End Dyn_ana.

Definition out_blue : ∀ n, con n :=
  λ n _, truth.

Definition ddd := SOME FARMER (λ m, SOME DONKEY (OWN m)).

Print FARMER. 
Print SOME.
Check (λ m, SOME FARMER (OWN m)).
