(* This file contains the definition of homogeneous vectors, basic operations on them, and relevant proofs. It also contains the type for the less-than relation, and applies them to indexing vectors *)

(* See CDS/Final versions/Vect.v for some of the heterogeneous vector stuff *)

(* TODO: add implicit arguments to jth, update uses of it in Dyn.v accordingly *)

Inductive Vect (A : Type) : nat -> Type := vnil : Vect A 0 | vcons : forall n : nat, A -> Vect A n -> Vect A (S n).
Arguments vnil {A}.
Arguments vcons {A} {n} _ _.

Module VectNotes.
    Declare Scope vect_scope.
    Notation "[]" := vnil (at level 0) : vect_scope.
    Infix "::" := vcons (at level 60, right associativity) : vect_scope.
    Open Scope vect_scope.
    Notation "[ x ]" := ((x :: [])) (at level 0) : vect_scope.
    Notation "[ x , .. , y ]" := ((vcons x .. (y :: []) ..)) (at level 0) : vect_scope.
End VectNotes.
Import VectNotes.

(* Basic operations on vectors *)
Module Vect_ops.
    (* The types for the head and tail functions, respectively *)
    Definition hdtype : Type -> nat -> Type
        :=  fun (A : Type) (n : nat) =>
            match n with
                | 0     => unit
                | S k   => A
            end.
    Definition tltype : Type -> nat -> Type
        :=  fun (A : Type) (n : nat) =>
            match n with
                | 0     => unit
                | S k   => Vect A k
            end.

    Definition head : forall {A : Type} {n : nat}, Vect A (S n) -> A
        :=  fun {A : Type} {n : nat} (v : Vect A (S n)) =>
            match v in (Vect _ m) return (hdtype A m) with
                | []        => tt
                | x :: xs   => x
            end.
    Definition tail : forall {A : Type} {n : nat}, Vect A (S n) -> Vect A n
        :=  fun {A : Type} {n : nat} (v : Vect A (S n)) =>
            match v in (Vect _ m) return (tltype A m) with
                | []        => tt
                | x :: xs   => xs
            end.

    (* Returns the last element of a non-empty vector *)
    Fixpoint last {A : Type} {n : nat} : Vect A (S n) -> A
        :=  match n as k return (Vect A (S k) -> A) with
                | 0     => head (* last element of a singleton vector is also its head *)
                | S i   => fun v : Vect A (S (S i)) => last (tail v)
            end.

    Fixpoint append {A : Type} {m n : nat} (u : Vect A m) (v : Vect A n) : Vect A (m+n)
        :=  match u in (Vect _ i) return (Vect A (i+n)) with
                | []        => v
                | x :: l    => x :: (append l v)
             end.
    Infix "++" := append (at level 60, right associativity) : vect_scope.

    (* splits a term v:(Vect A (m+n)) into a pair (Vect A m)*(Vect A n) *)
    Fixpoint vsplit_at {A : Type} (m n : nat) {struct m} : Vect A (m+n) -> (Vect A m)*(Vect A n)
        :=  match m as z return (Vect A (z+n) -> (Vect A z)*(Vect A n)) with
                | 0     => fun v : Vect A n => ([],v)
                | S i   => fun v : Vect A (S (i+n)) => let (l,r) := (vsplit_at i n (tail v)) in ((head v)::l,r)
                            (*  fun v : Vect A (S (i+n)) =>
                                prod_rect   (fun _ : (Vect A i)*(Vect A n) => ((Vect A (S i))*(Vect A n))%type)
                                            (fun xs : Vect A i => pair ((head v)::xs)) (v_split_at A i n (tail v)) *)
            end.

    (* take & drop basically are the first and second projections of vsplit_at- hoping to make induction easier using them *)
    Fixpoint take (A : Type) (m n : nat) {struct m} : Vect A (m+n) -> Vect A m
        :=  match m as k return (Vect A (k+n) -> Vect A k) with
                | 0     => fun _ : Vect A n => []
                | S i   => fun v : Vect A (S (i+n)) => (head v)::(take A i n (tail v))
            end.
    Fixpoint drop (A : Type) (m n : nat) {struct m} : Vect A (m+n) -> Vect A n
        :=  match m as k return (Vect A (k+n) -> Vect A n) with
                | 0     => fun v : Vect A n => v
                | S i   => fun v : Vect A (S (i+n)) => drop A i n (tail v)
            end.
    Arguments take {A} m {n} v.
    Arguments drop {A} m {n} v.

    (* Indexing on a vector by guaranteeing it contains the desired (mth) element, by requiring the vectors length to be S(m+n), for some n:nat *)
    Fixpoint nth {A : Type} (m : nat) {n : nat} : Vect A (S (m+n)) -> A
        :=  match m as k return (Vect A (S (k+n)) -> A) with
                | 0     => head
                | S i   => fun v : Vect A (S (S (i+n))) => nth i (tail v)
            end.
End Vect_ops.
Import Vect_ops.

(*  note: this can also be defined by recursion on the vector argument (and probably more legibly so);
    However, in what I've done with this stuff so far, often times it's easier to prove theorems where vmap is involved
    by recursing on the nat (eg, to prove the monad laws, since mu [the diagonal] must be defined by recursion over nat) *)
Fixpoint vmap {A B : Type} {n : nat} (f : A -> B) : Vect A n -> Vect B n
    :=  match n as k return (Vect A k -> Vect B k) with
            | 0     =>  fun v : Vect A 0     => []
            | S i   =>  fun v : Vect A (S i) => (f (head v)) :: (vmap f (tail v))
        end.
(* alt version of vmap via recursion on v *)
(*  Fixpoint vmap' {A B : Type} {n : nat} (f : A -> B) (v : Vect A n) : Vect B n
        :=  match v in (Vect _ k) return (Vect B k) with
                | []        => []
                | x :: r    => (f x)::(vmap' f r)
            end. *)

(* convert a vector of length m into a vector or length n, provided m=n (eg going from Vect A (a+b)+c to Vect A a+(b+c)) *)
Definition vcast : forall {A : Type} {m : nat}, Vect A m -> forall {n : nat}, m = n -> Vect A n
    := fun {A : Type} {m : nat} => eq_rect m (Vect A).

(* Type of proofs that vector u is a subvector of vector v *)
Inductive subvect {A : Type} : forall {m n : nat}, Vect A m -> Vect A n -> Prop
    :=  vbot : subvect [] []
    |   con1 : forall {m n : nat} (u : Vect A m) (v : Vect A n) (x : A), subvect u v -> subvect u (x :: v)
    |   con2 : forall {m n : nat} (u : Vect A m) (v : Vect A n) (x : A), subvect u v -> subvect (x :: u) (x :: v).
Infix "isSubvectof" := subvect (at level 30) : type_scope.
Infix "⊑" := subvect (at level 30) : type_scope.

Fixpoint max (m n : nat) : nat
    :=  match m with
            | 0     => n
            | S i   => S (match n with 0 => i | S j => max i j end)
        end.

(* defining this over all lengths, with 0-vectors mapping to 0 for simplicity *)
Fixpoint vmax {n : nat} : Vect nat n -> nat
    :=  match n with
            | 0     =>  fun _ : Vect nat 0 => 0
            | S i   =>  fun v : Vect nat (S i) => max (head v) (vmax (tail v))
        end.
(* Fixpoint vmax {n : nat} : Vect nat (S n) -> nat *)
    (* :=  match n with *)
            (* | 0     =>  head *)
            (* | S i   =>  fun v : Vect nat (S (S i)) => max (head v) (vmax (tail v)) *)
        (* end. *)
(* my old vmax, defined over vectors of all lengths and returns the smallest nat bigger than all of the elements of the input vector *)
    (* Fixpoint vmax {n : nat} : Vect nat n -> nat *)
        (* :=  match n as k return (Vect nat k -> nat) with *)
                (* | 0     =>  fun _ : Vect nat    0   => 0 *)
                (* | S i   =>  fun v : Vect nat (S i)  => max (S (head v)) (vmax (tail v)) *)
            (* end. *)


(* removing induction in recursive cases *)
Fixpoint m_frnt (m n k : nat) {struct m} : {x : nat | ((max m n)+k) = (m+x)}
    :=  match m as i,n as j return {x : nat | ((max i j)+k) = (i+x)} with
            | 0,j       =>  exist (fun x : nat => (j+k) = x) (j+k) eq_refl
            | S i,0     =>  exist (fun x : nat => (S (i+k)) = (S (i+x))) k eq_refl
            | S i,S j   =>  exist (fun x : nat => (S ((max i j)+k)) = (S (i+x)))
                                  (proj1_sig (m_frnt i j k)) (f_equal S (proj2_sig (m_frnt i j k)))
        end.

Fixpoint n_frnt (m n k : nat) {struct m} : {y : nat | ((max m n)+k) = (n+y)}
    :=  match m as i,n as j return {y : nat | ((max i j)+k) = (j+y)} with
            | 0,j       =>  exist (fun y : nat => (j+k) = (j+y)) k eq_refl
            | S i,0     =>  exist (fun y : nat => (S (i+k)) = y) (S (i+k)) eq_refl
            | S i,S j   =>  exist (fun y : nat => (S ((max i j)+k)) = (S (j+y)))
                                  (proj1_sig (n_frnt i j k)) (f_equal S (proj2_sig (n_frnt i j k)))
        end.

Definition id : forall {A : Type}, A -> A := fun {A : Type} (x : A) => x.
Definition comp : forall {A B C : Type}, (B -> C) -> (A -> B) -> A -> C := fun {A B C : Type} (f : B -> C) (g : A -> B) (x : A) => f (g x).
Infix "∘" := comp (at level 20).

(* A version of eq_ind for proving facts about equality proofs themselves *)
Definition eq_ind_dep : forall {A : Type} (x : A) (P : forall z : A, x = z -> Prop), P x eq_refl -> forall (y : A) (e : x = y), P y e
    :=  fun {A : Type} (x : A) (P : forall z : A, x = z -> Prop) (p : P x eq_refl) (y : A) (e : x = y) =>
        match e as d in (_ = z) return (P z d) with eq_refl => p end.


Section Vect_proofs.
    (* every 0-length vector is [], every (S i)-length vector is defined as its head cons'ed onto its tail *)
    Definition vfrmtyp : forall (A : Type) (k : nat), Vect A k -> Prop
        :=  fun (A : Type) (k : nat) =>
            match k as m return (Vect A m -> Prop) with
                | 0     => fun u : Vect A 0 => [] = u
                | S i   => fun u : Vect A (S i) => ((head u)::(tail u)) = u
            end.

    Definition Vect_form : forall {A : Type} {n : nat} (v : Vect A n), vfrmtyp A n v
        :=  fun {A : Type} {n : nat} (v : Vect A n) =>
            match v as u in (Vect _ k) return (vfrmtyp A k u) with
                | []    => eq_refl
                | x::xs => eq_refl
            end.

    (* Functor laws for vectors *)
    Definition funct1 : forall (A : Type) (n : nat) (v : Vect A n), (vmap id v) = v
        :=  fun A : Type => Vect_ind A  (fun (n : nat) (v : Vect A n) => (vmap id v) = v) eq_refl
                                        (fun (i : nat) (x : A) (r : Vect A i) (e : (vmap id r) = r) => f_equal (vcons x) e).

    Definition funct2 : forall (A B C : Type) (f : B -> C) (g : A -> B) (n : nat) (v : Vect A n),(vmap f (vmap g v)) = (vmap (f∘g) v)
        :=  fun (A B C : Type) (f : B -> C) (g : A -> B) =>
            Vect_ind A  (fun (n : nat) (v : Vect A n) => (vmap f (vmap g v)) = (vmap (f∘g) v)) eq_refl
                        (fun (i : nat) (x : A) (r : Vect A i) (e : (vmap f (vmap g r)) = (vmap (f∘g) r)) =>
                            f_equal (vcons (f (g x))) e).

    Definition vspl_app_inv : forall {A : Type} {m n : nat} (v : Vect A (m+n)), v = ((fst (vsplit_at m n v)) ++ (snd (vsplit_at m n v)))
        :=  fun {A : Type} {m n : nat} =>
            nat_ind (fun m : nat => forall (n : nat) (v : Vect A (m+n)), v = ((fst (vsplit_at m n v)) ++ (snd (vsplit_at m n v))))
                    (fun (n : nat) (v : Vect A n) => eq_refl)
                    (fun (i : nat) (f : forall (n : nat) (v : Vect A (i+n)), v = ((fst (vsplit_at i n v)) ++ (snd (vsplit_at i n v))))
                         (n : nat) (v : Vect A (S (i+n))) =>
                       eq_ind   ((head v)::(tail v))
                                (fun u : Vect A (S (i+n)) => u = ((fst (vsplit_at (S i) n u)) ++ (snd (vsplit_at (S i) n u))))
                                (eq_ind ((head v)::(fst (vsplit_at i n (tail v))),snd (vsplit_at i n (tail v)))
                                        (fun p : (Vect A (S i))*(Vect A n) => ((head v)::(tail v)) = ((fst p) ++ (snd p)))
                                        (f_equal (vcons (head v)) (f n (tail v)))
                                        (let (l,r) := (vsplit_at i n (tail v)) in ((head v)::l,r))
                                        (prod_ind   (fun p : (Vect A i)*(Vect A n) => ((head v)::(fst p),snd p)
                                                            = (let (l,r) := p in ((head v)::l,r)))
                                                    (fun (l : Vect A i) (r : Vect A n) => eq_refl)
                                                    (vsplit_at i n (tail v))))
                                v
                                (Vect_form v)) m n.

    (* Associativity of (++), starting with a proof of the associativity of (+) *)
    Fixpoint add_assoc (m n p : nat) {struct m} : ((m+n)+p) = (m+(n+p))
        := match m as i return (((i+n)+p) = (i+(n+p))) with 0 => eq_refl | S i => f_equal S (add_assoc i n p) end.

    Definition app_assoc : forall {A : Type} {m n p : nat} (u : Vect A m) (v : Vect A n) (w : Vect A p), (eq_rect ((m+n)+p) (Vect A) ((u++v)++w) (m+(n+p)) (add_assoc m n p)) = (u++(v++w))
        :=  fun {A : Type} {m n p : nat} (u : Vect A m) (v : Vect A n) (w : Vect A p) =>
            Vect_ind A
                (fun (i : nat) (r : Vect A i) => (eq_rect ((i+n)+p) (Vect A) ((r++v)++w) (i+(n+p)) (add_assoc i n p)) = (r++(v++w)))
                eq_refl
                (fun (i : nat) (x : A) (r : Vect A i)
                     (e : (eq_rect ((i+n)+p) (Vect A) ((r++v)++w) (i+(n+p)) (add_assoc i n p)) = (r++(v++w))) =>
                     eq_trans   (eq_ind_dep ((i+n)+p)
                                    (fun (z : nat) (d : ((i+n)+p) = z) =>
                                        (eq_rect (S ((i+n)+p)) (Vect A) (x::((r++v)++w)) (S z) (f_equal S d))
                                            = (x::(eq_rect ((i+n)+p) (Vect A) ((r++v)++w) z d)))
                                    eq_refl (i+(n+p)) (add_assoc i n p))
                                (f_equal (vcons x) e))
                m u.

    Definition tkdr_app_inv : forall {A : Type} (m : nat) {n : nat} (v : Vect A (m+n)), v = ((take m v) ++ (drop m v))
        :=  fun {A : Type} (m : nat) {n : nat} =>
            nat_ind (fun i : nat => forall v : Vect A (i+n), v = ((take i v) ++ (drop i v)))
                    (@eq_refl (Vect A n))
                    (fun (i : nat) (f : forall r : Vect A (i+n), r = ((take i r) ++ (drop i r))) (v : Vect A (S (i+n))) =>
                        eq_trans (eq_sym (Vect_form v)) (f_equal (vcons (head v)) (f (tail v)))) m.

    (* take/drop of a vector (l++r) is equal to l/r, respectively *)
    Definition tkdr_app_inv2a : forall {A : Type} (m : nat) {n : nat} (u : Vect A m) (v : Vect A n), u = (take m (u++v))
        :=  fun {A : Type} (m : nat) {n : nat} (u : Vect A m) (v : Vect A n) =>
            Vect_ind A  (fun (i : nat) (l : Vect A i) => l = (take i (l ++ v))) eq_refl
                        (fun (i : nat) (x : A) (l : Vect A i) (e : l = (take i (l ++ v))) => f_equal (vcons x) e) m u.
    Definition tkdr_app_inv2b : forall {A : Type} (m : nat) {n : nat} (u : Vect A m) (v : Vect A n), v = (drop m (u++v))
        :=  fun {A : Type} (m : nat) {n : nat} (u : Vect A m) (v : Vect A n) =>
            Vect_ind A  (fun (i : nat) (l : Vect A i) => v = (drop i (l ++ v))) eq_refl
                        (fun (i : nat) (_ : A) (l : Vect A i) (e : v = (drop i (l ++ v))) => e) m u.

    Definition drop_assoc : forall {A : Type} (m n k : nat) (v : Vect A ((m+n)+k)), (drop (m+n) v) = (drop n (drop m (vcast v (add_assoc m n k))))
        :=  fun {A : Type} (m n k : nat) =>
            nat_ind (fun i : nat => forall v : Vect A ((i+n)+k), (drop (i+n) v) = (drop n (drop i (vcast v (add_assoc i n k)))))
                    (fun v : Vect A (n+k) => eq_refl)
                    (fun (i : nat) (f : forall v : Vect A ((i+n)+k), (drop (i+n) v) = (drop n (drop i (vcast v (add_assoc i n k)))))
                         (v : Vect A (S ((i+n)+k))) =>
                        eq_trans    (f (tail v))
                                    (f_equal    (fun u : Vect A (i+(n+k)) => (drop n (drop i u)))
                                                (eq_ind_dep ((i+n)+k)
                                                            (fun (z : nat) (d : ((i+n)+k) = z) =>
                                                                (vcast (tail v) d) = (tail (vcast v (f_equal S d))))
                                                            eq_refl (i+(n+k)) (add_assoc i n k))))
                    m.
End Vect_proofs.

(* less than relation, simple lemmas, definition of indexing a vector using a proof of the index being in range *)
(* Now obsolete; using the leq relation instead *)
Section Less_Than.
    Inductive lthan : nat -> nat -> Prop := Zbotl : forall n : nat, lthan 0 (S n) | SPrevl : forall m n : nat, lthan m n -> lthan (S m) (S n).
    Infix "<" := lthan (at level 70).

    Definition Zleft : forall n : nat, ~ n < 0 := fun (n : nat) (e : n < 0) => match e in (_ < m) return (if m return Prop then False else True) with Zbotl _ | _ => I end.

    Definition Lt_inj : forall m n : nat, (S m) < (S n) -> m < n
        :=  fun (m n : nat) (e : S m < S n) =>
            match e in (i < j) return (match i return Prop with 0 => True | S x => (match j return Prop with 0 => True | S y => x < y end) end) with
                | Zbotl _       => I
                | SPrevl i j d  => d
            end.

    Definition ith : forall (A : Type) (m : nat), Vect A m -> forall n : nat, n < m -> A
        :=  fun A : Type =>
            Vect_rect A (fun (m : nat) (_ : Vect A m) => forall n : nat, n < m -> A)
                        (fun (n : nat) (e : n < 0) => False_rect A (Zleft n e))
                        (fun (i : nat) (x : A) (_ : Vect A i) (f : forall n : nat, n < i -> A) (n : nat) =>
                            match n return (n < S i -> A) with
                                | 0     => fun _ :   0 < S i => x
                                | S j   => fun e : S j < S i => f j (Lt_inj j i e)
                            end).

    (* Quick check/examples of the ith function in action *)
    (* Eval compute in (ith nat 4 [4,6,2,9] 0 (Zbot 3)).  *)                                      (* = 4 *)
    (* Eval compute in (ith nat 4 [4,6,2,9] 1 (SPrev 0 3 (Zbot 2))). *)                           (* = 6 *)
    (* Eval compute in (ith nat 4 [4,6,2,9] 2 (SPrev 1 3 (SPrev 0 2 (Zbot 1)))). *)               (* = 2 *)
    (* Eval compute in (ith nat 4 [4,6,2,9] 3 (SPrev 2 3 (SPrev 1 2 (SPrev 0 1 (Zbot 0))))). *)   (* = 9 *)

    (* transitivity of the less than relation *)
    Definition lt_trans : forall m n p : nat, m < n -> n < p -> m < p
        :=  fun (m n p : nat) (l : m < n) =>
            lthan_ind   (fun i j : nat => forall k : nat, j < k -> i < k)
                        (fun i k : nat =>
                            match k as z return ((S i) < z -> 0 < z) with
                                | 0     => fun s : S i <   0 => False_ind (0 < 0) (Zleft (S i) s)
                                | S z   => fun _ : S i < S z => Zbotl z
                            end)
                        (fun (i j : nat) (_ : i < j) (f : forall z : nat, j < z -> i < z) (k : nat) =>
                            match k as z return ((S j) < z -> (S i) < z) with
                                | 0     => fun t : (S j) <    0  => False_ind ((S i) < 0) (Zleft (S j) t)
                                | S z   => fun t : (S j) < (S z) => SPrevl i z (f z (Lt_inj j z t))
                            end)
                        m n l p.
End Less_Than.
(* Infix "<" := lthan (at level 70). *)

(* Trying to use leq as primitive instead of lthan- seems promising for def of udyn *)
Module Import   Leq.
    Inductive leq : nat -> nat -> Prop := Zbot : forall k : nat, leq 0 k | Sprev : forall i j : nat, leq i j -> leq (S i) (S j).
    Infix "≤v"   := leq  (at level 20) : type_scope.

    (* likely not necessary *)
    Definition leq_ind_dep  : forall P : forall m n : nat, m ≤v n -> Prop, (forall k : nat, P 0 k (Zbot k))
                                -> (forall (i j : nat) (r : i ≤v j), P i j r -> P (S i) (S j) (Sprev i j r))
                                ->  forall (m n : nat) (l : m ≤v n), P m n l
        :=  fun (P : forall m n : nat, m ≤v n -> Prop) (f : forall k : nat, P 0 k (Zbot k))
                (g : forall (i j : nat) (r : i ≤v j), P i j r -> P (S i) (S j) (Sprev i j r)) =>
            fix Foo (m n : nat) (l : m ≤v n) {struct l} : P m n l :=
            match l as u in (x ≤v y) return (P x y u) with Zbot k => f k | Sprev i j r => g i j r (Foo i j r) end.
    Definition leq'_ind'    : forall (m : nat) (P : nat -> Prop), P m -> (forall j : nat, m ≤v j -> P j -> P (S j))
                            -> forall n : nat, m ≤v n -> P n
        :=  fun (m : nat) (P : nat -> Prop) (b : P m) (f : forall j : nat, m ≤v j -> P j -> P (S j)) (n : nat) (l : m ≤v n) =>
            leq_ind (fun x y : nat => forall Q : nat -> Prop, Q x -> (forall j : nat, x ≤v j -> Q j -> Q (S j)) -> Q y)
                    (fun (k : nat) (Q : nat -> Prop) (c : Q 0) (g : forall j : nat, 0 ≤v j -> Q j -> Q (S j)) =>
                        nat_ind Q c (fun j : nat => g j (Zbot j)) k)
                    (fun (i j : nat) (_ : i ≤v j)
                         (g : forall R : nat -> Prop, R i -> (forall k : nat, i ≤v k -> R k -> R (S k)) -> R j)
                         (Q : nat -> Prop) (d : Q (S i)) (h : forall k : nat, (S i) ≤v k -> Q k -> Q (S k)) =>
                        g (fun k : nat => Q (S k)) d (fun (k : nat) (p : i ≤v k) => h (S k) (Sprev i k p)))
                    m n l P b f.

    Definition lt   : nat -> nat -> Prop := fun m n : nat => (S m) ≤v n.
    (* default interpretation of < is in nat_scope, so putting this in type_scope leads to that other one being the default *)
    Infix "<" := lt.
End             Leq.

Section leq_prfs.
    Definition leq_refl     : forall m : nat, m ≤v m
        := nat_ind (fun m : nat => m ≤v m) (Zbot 0) (fun i : nat => Sprev i i).

    Definition leq_trans    : forall m n p : nat, m ≤v n -> n ≤v p -> m ≤v p
        :=  fun (m n p : nat) (l : m ≤v n) =>
            leq_ind (fun i j : nat => forall k : nat, j ≤v k -> i ≤v k)
                    (fun (i j : nat) (_ : i ≤v j) => Zbot j)
                    (fun (i j : nat) (_ : i ≤v j) (f : forall z : nat, j ≤v z -> i ≤v z) (k : nat) (q : (S j) ≤v k) =>
                        (match q in (x ≤v y)
                         return (match x return Prop with 0 => True | S z => (forall k : nat, z ≤v k -> i ≤v k) -> (S i) ≤v y end) with
                            | Zbot    _     => I
                            | Sprev x y t   => fun g : forall k : nat, x ≤v k -> i ≤v k => Sprev i y (g y t)
                       end) f)
                    m n l p.

    Definition zsmall       : forall m : nat, m ≤v 0 -> 0 = m
        :=  fun (m : nat) (l : m ≤v 0) =>
            match l in (i ≤v j) return (if j return Prop then (0 = i) else (0 = 0))
            with Zbot 0 | Zbot (S _) | Sprev _ _ _ => eq_refl end.

    Definition leq_inj      : forall m n : nat, (S m) ≤v (S n) -> m ≤v n
        :=  fun (m n : nat) (l : (S m) ≤v (S n)) =>
            match l in (i ≤v j) return ((pred i) ≤v (pred j)) with Zbot k => Zbot (pred k) | Sprev i j r => r end.

    Definition max_lub_1    : forall m n : nat, m ≤v (max m n)
        :=  nat_ind (fun m : nat => forall n : nat, m ≤v (max m n)) Zbot
                    (fun (i : nat) (f : forall j : nat, i ≤v (max i j)) (n : nat) =>
                     match n as y return ((S i) ≤v (max (S i) y)) with 0 => leq_refl (S i) | S j => Sprev i (max i j) (f j) end).
    Definition max_lub_2    : forall m n : nat, n ≤v (max m n)
        :=  nat_ind (fun m : nat => forall n : nat, n ≤v (max m n)) leq_refl
                    (fun (i : nat) (f : forall j : nat, j ≤v (max i j)) (n : nat) =>
                     match n as y return (y ≤v (max (S i) y)) with 0 => Zbot (S i) | S j => Sprev j (max i j) (f j) end).
End leq_prfs.

(* same as ith, just using leq as the primitive instead of lthan *)
Definition jth : forall (A : Type) (m : nat), Vect A m -> forall n : nat, n < m -> A
    :=  fun A : Type =>
        Vect_rect A (fun (m : nat) (_ : Vect A m) => forall n : nat, n < m -> A)
                    (fun (n : nat) (l : (S n) ≤v 0) => eq_rect 0 (fun z : nat => match z with 0 => True | S _ => A end) I (S n) (zsmall (S n) l))
                    (fun (i : nat) (x : A) (_ : Vect A i) (f : forall n : nat, n < i -> A) (n : nat) =>
                        match n as y return (y < (S i) -> A) with
                            | 0     => fun _ : 0 < (S i) => x
                            | S j   => fun r : (S j) < (S i) => f j (leq_inj (S j) i r)
                        end).

(* this is the function implementing the X_N notation for dyn *)
Definition imap : forall {i : nat} (u : Vect nat i) {n : nat} {A : Type}, Vect A n -> (vmax u) < n -> Vect A i
    :=  fun {i : nat} (u : Vect nat i) {n : nat} {A : Type} (v : Vect A n) =>
        Vect_rect nat   (fun (m : nat) (l : Vect nat m) => (vmax l) < n -> Vect A m)
                        (fun _ : (vmax []) < n => [])
                        (fun (m x : nat) (l : Vect nat m) (f : (vmax l) < n -> Vect A m) (r : (vmax (x::l)) < n) =>
                         (jth A n v x (leq_trans (S x) (S (max x (vmax l))) n (Sprev x (max x (vmax l)) (max_lub_1 x (vmax l))) r))
                           :: (f (leq_trans (S (vmax l)) (S (max x (vmax l))) n (Sprev (vmax l) (max x (vmax l)) (max_lub_2 x (vmax l))) r)))
                        i u.

(* simple addition proofs; move add_assoc to here? *)
Definition Zria : forall n : nat, (n+0) = n
    := nat_ind (fun n : nat => (n+0) = n) eq_refl (fun (i : nat) (e : (i+0) = i) => f_equal S e).
Definition Sdistr : forall m j : nat, (m+(S j)) = (S (m+j))
    := fun m j : nat => nat_ind (fun i : nat => (i+(S j)) = (S (i+j))) eq_refl (fun (i : nat) (e : (i+(S j)) = (S (i+j))) => f_equal S e) m.
Definition add_comm : forall m n : nat, (m+n) = (n+m)
    := fun m : nat => nat_ind (fun n : nat => (m+n) = (n+m)) (Zria m) (fun (j : nat) (e : (m+j) = (j+m)) => eq_trans (Sdistr m j) (f_equal S e)).
Definition assoc_flip   : forall m n k : nat, (m+(n+k)) = ((m+k)+n)
    := fun m n k : nat => nat_ind (fun i : nat => (i+(n+k)) = ((i+k)+n)) (add_comm n k) (fun (i : nat) (e : (i+(n+k)) = ((i+k)+n)) => f_equal S e) m.

(* vector currying/uncurrying *)
Section Curry.
    Fixpoint prd (n : nat) (A B : Type) {struct n} : Type
        :=  match n with
                | 0     =>  B
                | S i   =>  A -> prd i A B
            end.

    Fixpoint vcur (n : nat) (A B : Type) {struct n} : (Vect A n -> B) -> prd n A B
        :=  match n with
                | 0     => fun f : Vect A 0 -> B => f []
                | S i   => fun (f : Vect A (S i) -> B) (x : A) => vcur i A B (fun v : Vect A i => f (x::v))
            end.
    Fixpoint vuncur (n : nat) (A B : Type) {struct n} : prd n A B -> Vect A n -> B
        :=  match n with
                | 0     => fun (y : B) (_ : Vect A 0) => y
                | S i   => fun (f : A -> prd i A B) (v : Vect A (S i)) => vuncur i A B (f (head v)) (tail v)
            end.
End Curry.
