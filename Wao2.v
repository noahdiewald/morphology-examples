(** * Wao Tededo Fragment for Dissertation

This file provides a morphological fragment of Wao Terero pattern
using a version of my theoretical framework as it was defined at the
time of my dissertation. *)

(** The quasi phonemic representation of morphological forms use the
string definition from the standard library. *)

Require Import Coq.Strings.String.

(** I use unicode in this file. *)

Require Import Coq.Unicode.Utf8.

(** I use lists as a convenient data structure. *)

Require Import Coq.Lists.List.

Open Scope type_scope.
Open Scope string_scope.

(** `m` are basic symbols used to form category names.  Associated
types, functions and relations will have ₘ in their name.  The
comments below are not intended to 'define' the catagories, but to
provide some intuition with the meanings and forms they are commonly
associated with. *)

Inductive m : Set :=
| Yẽdẽₘ (* The stem of the adjective 'big'. *)
| Giitãₘ (* The stem of the adjective 'small'. *)
| Bãdĩₘ (* The stem of the proximal demonstrative. *)
| Adoₘ (* The stem of 'same' and the numeral 'one'. *)
| Ĩₘ (* The stem of the copula, short third person pronouns and the
  distal demonstrative. *)
| Tõbẽₘ (* The stem of long form pronouns. *)
| Dãtaₘ (* The stem of the verb 'to ache'. *)
| Goₘ (* The stem of the verb 'to go'. *)
| Poₘ (* The stem of the verb 'to come'. *)
| Eₘ (* The stem of the verb 'to get'. *)
| Keₘ (* The stem of the verb 'to do'. *)
| Kẽₘ (* The stem of the verb 'to eat' or 'to cut'. *)
| Diₘ (* The bound stem of the noun 'stone'. *)
| Aₘ (* The bound stem of the noun 'plant'. *)
| Wiₘ (* The bound stem of the noun 'canoe'. *)
| boₘ (* The first person singular suffix. *)
| bõₘ (* The non-singular first person suffix. *)
| daₘ (* The dual suffix. *)
| dãₘ (* The feminen suffix. *)
| diₘ (* The plural person suffix. *)
| teₘ (* The gerundive suffix. *)
| kaₘ (* The 'fruit' lexical suffix. *)
| keₘ (* The limitive suffix. *)
| kãₘ (* The third person sentient suffix. *)
| pẽₘ (* The 'liquid' lexical suffix. *)
| poₘ (* The 'hand' lexical suffix. *)
| wẽₘ. (* The 'plant' lexical suffix. *)

(** Some `m` correspond to `stems` *)

Definition stems : list m :=
  Yẽdẽₘ :: Giitãₘ :: Kẽₘ :: Dikaₘ :: Awẽₘ :: Wipoₘ :: nil.

(** Using lists of `m` instances, category names `Mₘ` are licensed. *)

Axiom Mₘ : (list m) → Prop.

(** A partial order is defined over `m` lists, where only `M`
instances are ordered. *)

Inductive leₘ : (list m) → (list m) → Prop :=
| reflₘ : ∀ α, Mₘ α → leₘ α α
| transₘ : ∀ α β γ, Mₘ α → Mₘ β → Mₘ γ → leₘ α β → leₘ β γ → leₘ α γ. 

Axiom antisymₘ : ∀ α β : (list m), leₘ α β → leₘ β α → α = β.

Infix "≤ₘ" := leₘ (at level 60, right associativity).

(** K are names of form classes, similar in concept to inflection
classes.  The uppercase kappa `K' is a mnemonic for /klæs/.  Like ₘ
the ₖ is used for names of types, functions and relations associated
with K.  Variables of type K are written as κ or κₙ. The noneₖ class
is for the nil case of a list of categories. It has no theoretical
meaning. *)

Inductive K : Set :=
| adjₖ
| vₖ
| dikaₖ
| awẽₖ
| wipoₖ
| keweₖ
| teₖ
| noneₖ.

(** Form classes are ordered. *)
    
Inductive leₖ : K → K → Prop :=
| reflₖ : ∀ α, leₖ α α
| transₖ : ∀ α β γ, leₖ α β → leₖ β γ → leₖ α γ.

Axiom antisymₖ : ∀ α β, leₖ α β → leₖ β α → α = β.

Infix "≤ₖ" := leₖ (at level 60, right associativity).

(** A subset of (list) m types are stems.
They may not be free so they may not correspond to a Mₘ. *)

Fixpoint klass (α : list m) : K :=
  match α with
  | nil => noneₖ
  | wẽₘ :: Kẽₘ :: nil => keweₖ
  | de :: Kẽₘ :: nil => keweₖ
  | Yẽdẽₘ :: nil => adjₖ
  | Giitãₘ :: nil => adjₖ
  | Kẽₘ :: nil => vₖ
  | Teₘ :: nil => teₖ
  | Dikaₘ :: nil => dikaₖ
  | Awẽₘ :: nil => awẽₖ
  | Wipoₘ :: nil => wipoₖ
  | _ :: α' => klass α'
  end.

(** Rather than eagerly building up strings, morphological rules build
a list of processes that are applied at some point of evaluation, such
as evaluating string equality.  The `applyₚᵣ' function applies all of
the processes in order to the empty string.  Processes and process
related functions have a ₚᵣ subscript. *)

Fixpoint applyₚᵣ (processes : list ((string → string) → (string → string))) (acc : string → string) : string :=
  match processes, acc with
  | nil, acc' => acc' ""
  | p :: ps, acc' => applyₚᵣ ps (p acc')
  end.

(** Processes are not string to string functions but functions from
string to string functions to string to string functions.  Stems,
notably, take an input string to string function and return a
constant-like function, which disgards its input.  *)

Definition awẽₚᵣ (p : string → string) : (string → string) :=
  λ (_ : string), p "a".

Definition dikaₚᵣ (p : string → string) : (string → string) :=
  λ (_ : string), p "di".

Definition yẽdẽₚᵣ (p : string → string) : (string → string) :=
  λ (_ : string), p "yẽdẽ".

Definition giitãₚᵣ (p : string → string) : (string → string) :=
  λ (_ : string), p "giitã".

Definition wẽₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "wẽ").

Definition kaₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "ka").

Definition kãₚᵣ (p : string → string) : (string → string) :=
  λ (stem : string), p (stem ++ "kã").

(** The `idₚᵣ' function is used as input the result of applying
processes. *)

Definition idₚᵣ (s : string) : string := s.

(** The example below demonstrates how processes result in a string *)

Example yẽdẽwẽ_application:
  applyₚᵣ (wẽₚᵣ :: yẽdẽₚᵣ :: nil) idₚᵣ = "yẽdẽwẽ".
Proof.
  simpl.
  reflexivity.
Qed.

(** The data structure used by the form paradigm is a pair of a
category and a string. *)

Definition structₘₚ := (list m * list ((string → string) → string → string)).
  
(** A form to form mapping rule has the following structure.  There is
an input compound category, a form class constraint, a new category
that will be added to the compound category and a new process to be
added to the process list. *)

Definition rule1ₘₚ (catₘ : list m) (κ : K) (newₘ : m) (newₚᵣ : (string → string) → string → string) :=
  λ (α : structₘₚ)
    (proofₘ : fst α ≤ₘ catₘ)
    (proofₖ : klass (fst α) ≤ₖ κ),
    (newₘ :: fst α, newₚᵣ :: snd α).

Definition rule2ₘₚ (catₘ : list m) (κ : K) (newₘ : m) (newₚᵣ : (string → string) → string → string) :=
  λ (α : structₘₚ)
    (proofₘ : fst α ≤ₘ catₘ)
    (proofₖ : klass (fst α) ≤ₖ κ),
    (newₘ :: (tail (fst α)), newₚᵣ :: (tail (snd α))).

Inductive FEₘₚ : structₘₚ → Prop :=
| yẽdẽMP : FEₘₚ ( Yẽdẽₘ :: nil, yẽdẽₚᵣ :: nil )
| giitaMP : FEₘₚ ( Giitãₘ :: nil, giitãₚᵣ :: nil )
| awẽMP : FEₘₚ ( wẽₘ :: Awẽₘ :: nil, wẽₚᵣ :: awẽₚᵣ :: nil )
| dikaMP : FEₘₚ ( kaₘ :: Dikaₘ :: nil, kaₚᵣ :: dikaₚᵣ :: nil )
| wẽMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule2ₘₚ (baseₘ :: nil) adjₖ wẽₘ wẽₚᵣ) α proofₘ proofₖ)
| kãMP : ∀ α proofₘ proofₖ,
    FEₘₚ α → FEₘₚ ((rule1ₘₚ (baseₘ :: nil) adjₖ kãₘ kãₚᵣ) α proofₘ proofₖ).

(** Anything that is proveably a form paradigm member has a validly
named compound category. *)

Definition FEM : ∀ α : structₘₚ, FEₘₚ α → Prop :=
  λ (α : structₘₚ) (_ : FEₘₚ α), Mₘ (fst α).

Definition m_dec : ∀ α β : m, {α = β} + {α <> β}.
Proof. decide equality. Qed.
Definition eqₘ α β := if m_dec α β then true else false.

Fixpoint stemof (α : list m) : option m :=
  match α with
  | nil => None
  | head :: tail =>
      match (find (eqₘ head) stems) with
      | None => stemof tail
      | something => something
      end
  end.

Definition optional_stem_eq (α : option m) (β : option m) : bool :=
  match α, β with
  | None, _ => false
  | _, None => false
  | Some x, Some y => eqₘ x y
  end.

Definition eq_stem (α : structₘₚ) (β : structₘₚ) : bool :=
  match α, β with
  | (x, _), (y, _) => optional_stem_eq (stemof x) (stemof y)
  end.

Definition S (α : structₘₚ) (β : structₘₚ) : Prop :=
  eq_stem α β = true.

Inductive FPₘₚ : structₘₚ → structₘₚ → Prop :=
| inₘₚ : ∀ α β, S α β → FEₘₚ α → FEₘₚ β → FPₘₚ α β
| 
  

(** Form paradigm string equivalence states that when two structures
that have process lists that reduce to the same string, they are
equivalent, so long as their compound categories are valid names.  It
may be that the string is produced by distinct process lists or that
the compound category is different.  The str_equivₘₚ constructor
states that they are never the less equivalent, equal strings are the
determining factor. If two structures are equivalent, compound
categories may be swapped. *)

Inductive equivₘₚ : structₘₚ → structₘₚ → Prop :=
| reflₘₚ : ∀ α : structₘₚ, Mₘ (fst α) → equivₘₚ α α
| symₘₚ : ∀ α β : structₘₚ, Mₘ (fst α) → Mₘ (fst β) → equivₘₚ α β → equivₘₚ β α
| transₘₚ : ∀ α β γ, Mₘ (fst α) → Mₘ (fst β) → Mₘ (fst γ) → equivₘₚ α β → equivₘₚ β γ → equivₘₚ α γ
| str_equivₘₚ : ∀ α β : structₘₚ, Mₘ (fst α) → Mₘ (fst β) → applyₚᵣ (snd α) = applyₚᵣ (snd β) → equivₘₚ α β
| cat_equivₘₚ : ∀ α β : structₘₚ, Mₘ (fst α) → Mₘ (fst β) → equivₘₚ α β → equivₘₚ α (fst β, snd α).

Infix "≡ₘₚ" := equivₘₚ (at level 90).

(** Here I wish to prove that not only the left side of the
equivalence (α) but also the right side (β) has category equivalence.
If two structures are string equivalent, then the left side structure
may have its compound category replaced with the compound category of
the right side structure, as stated in `cat_equivₘₚ'.  Due to the
symmetric property of the equivalence, the right side structure may
also have its compound category replaced with the compound category of
the left side structure. *)

Lemma rev_cat_equivₘₚ : ∀ α β : structₘₚ, α ≡ₘₚ β → β ≡ₘₚ (fst α, snd β).
Proof.
  (** The statement `intros α β H' introduces the variables and the hypothesis α ≡ₘₚ β.
     This results in the following labeled hypotheses and goal.
   *)

  (**
     α, β : structₘₚ
     H : α ≡ₘₚ β
     ============================
     β ≡ₘₚ (fst α, snd β)

   *) 
  intros α β H.
  
  (** The statement `apply symₘₚ in H' applies the type constructor to
  the hypothesis H.

     This results in the order of the variables in the hypothesis H
   being flipped.  *)

  (**
     α, β : structₘₚ
     H : β ≡ₘₚ α
     ============================
     β ≡ₘₚ (fst α, snd β)

   *)
  apply symₘₚ in H.
  
  (* The statement `apply cat_equivₘₚ in H' applies the type constructor to the hypothesis H.

     This results in the hypothesis H being identical to the goal.

     α, β : structₘₚ
     H : β ≡ₘₚ (fst α, snd β)
     ============================
     β ≡ₘₚ (fst α, snd β)

   *)
  apply cat_equivₘₚ in H.

  (* The `assumption' tactic causes the proof assistant to look for a type that is convertable to the goal in the context.
     In this case H is trivially convertable.
   *)
  assumption.
Qed.

(** The next two proofs demonstrate that the string equivalence definition results in the equivalence of the processes that produced the identical strings. *)

Lemma proc_equivₘₚ : ∀ α β : structₘₚ, α ≡ₘₚ β → α ≡ₘₚ (fst α, snd β).
Proof.
  intros α β H.

  (* The statement `apply rev_cat_equivₘₚ in H as I' applies the previous lemma to the hypothesis H.
     The result of the application is labeled I so that both hypothesis can be referenced later.

     The result is the following set of hypotheses and goals.

     α, β : structₘₚ
     H : α ≡ₘₚ β
     I : β ≡ₘₚ (fst α, snd β)
     ============================
     α ≡ₘₚ (fst α, snd β)
   *)
  apply rev_cat_equivₘₚ in H as I.

  (* The statement `apply transₘₚ with α β (fst α, snd β) in I' applies the type constructor for transitivity, explicitly specifying the arguments.

     This results in I being identical to goal.
     The proof assistant requires the second goal to be proven due to the definition of `transₘₚ'.
     The second goal corresponds to H.
     Both goals can be solved by assumption.

     α, β : structₘₚ
     H : α ≡ₘₚ β
     I : α ≡ₘₚ (fst α, snd β)
     ============================
     α ≡ₘₚ (fst α, snd β)

     goal 2 is:
     α ≡ₘₚ β
 
   *)
  apply transₘₚ with α β (fst α, snd β) in I.
  assumption.
  assumption.
Qed.

(** The lemma for the reverse case of `proc_equivₘₚ' only requires the symmetric property of `≡ₘₚ' to be proven. *)

Lemma rev_proc_equivₘₚ : ∀ α β : structₘₚ, α ≡ₘₚ β → β ≡ₘₚ (fst β, snd α).
Proof.
  intros α β H.
  apply symₘₚ in H.
  apply proc_equivₘₚ in H as I.
  assumption.
Qed.
