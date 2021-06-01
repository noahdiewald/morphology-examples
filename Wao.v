(** * Wao Tededo Fragment
    
The purpose of this file is to eventually lay out a significant
grammatical fragment of Wao Tededo, beginning with a simple treatment
of adjectival classifiers. It is also a place where I plan to
implement various innovations of the underlying formalism. *)

Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.

Open Scope type_scope.  Open Scope string_scope.

(** The quasi phonological representation of morphological forms use
the string definition from the standard library. *)

Inductive mₘ : Set :=
| baseₘ
| poₘ
| concatₘ : mₘ → mₘ → mₘ.

Infix "⊙" := concatₘ (at level 60, right associativity).

(** mₘ is a kind of ad hoc name for some basic symbols used to form
category names. *)

Inductive Mₘ : mₘ → Prop :=
| baseM : Mₘ baseₘ
| poM : Mₘ poₘ.

(** Using mₒ instances, a finite number of category names are
licensed. *)

Inductive leₘ : mₘ → mₘ → Prop :=
| reflₘ : ∀ α, Mₘ α → leₘ α α
| transₘ : ∀ α β γ, Mₘ α → Mₘ β → Mₘ γ → leₘ α β → leₘ β γ → leₘ α γ. 

Axiom antisymₘ : ∀ α β : mₘ, leₘ α β → leₘ β α → α = β.

Infix "≤ₘ" := leₘ (at level 60, right associativity).

(** A partial order is defined over mₒ instances, where only Mₖ
instances are ordered. *)

Inductive lₗ : Set :=
| ñeneₗ (* big *)
| giitaₗ. (* small *)

(** Lexemes are defined as a simple inductive type. *)

Inductive kₖ : Set :=
| adjₖ
| anyₖ.
                                              
Inductive leₖ : kₖ → kₖ → Prop :=
| topₖ : ∀ α β, α = anyₖ → leₖ α β
| reflₖ : ∀ α, leₖ α α
| transₖ : ∀ α β γ, leₖ α β → leₖ β γ → leₖ α γ.

Axiom antisymₖ : ∀ α β, leₖ α β → leₖ β α → α = β.

Infix "≤ₖ" := leₖ (at level 60, right associativity).

(** Form classes are ordered with anyₖ as a top. *)

Definition fₗₖ (α : lₗ) : kₖ :=
  match α with
  | ñeneₗ => adjₖ
  | giitaₗ => adjₖ
  end.

(** Each lexeme has a form class *)

Definition poₜ (stem : string) : string :=
  stem ++ "po".

Definition mpₘₚ := (mₘ * string).
                        
(** poₜ is a simple rule for suffixing the sting "po" to a base. *)

Definition ruleₘₚ (m : mₘ) (k : kₖ) (newₘ : mₘ) (t : string → string) :=
  λ (α : mpₘₚ)
    (l : lₗ)
    (proofₘ : fst α ≤ₘ m)
    (proofₖ : fₗₖ l ≤ₖ k), (newₘ, t (snd α)).

Inductive MPₘₚ : mpₘₚ → lₗ → Prop :=
| ñeneMP : MPₘₚ (baseₘ, "ñene") ñeneₗ
| giitaMP : MPₘₚ (baseₘ, "giita") giitaₗ  
| poMP : ∀ α l proofₘ proofₖ,
    MPₘₚ α l → MPₘₚ ((ruleₘₚ baseₘ adjₖ poₘ poₜ) α l proofₘ proofₖ) l.

(** MPₘₚ is a predicate for determining form paradigm entries. *)

Inductive Pₘₚ : mpₘₚ → mpₘₚ → Prop :=
| inₘₚ : ∀ α β l, MPₘₚ α l → MPₘₚ β l → Pₘₚ α β
| reflₘₚ : ∀ α l, MPₘₚ α l → Pₘₚ α α
| transₘₚ : ∀ α β γ, Pₘₚ α β → Pₘₚ β γ → Pₘₚ α γ
| symₘₚ : ∀ α β, Pₘₚ α β → Pₘₚ β α.

(** The form paradigm for some lexeme is an equivalence class *)

Inductive ϕ : Set :=
| ε
| η : string → ϕ
| concatϕ (α β : ϕ).

Infix "•" := concatϕ (at level 60, right associativity).

(** The pheno is simplified. *)

Inductive τ : Set :=
| NP
| N
| Fin
| infτ (α β : τ).

Notation "x ⊸ y" := (infτ x y) (at level 60, right associativity).

(** The tecto is simplified. *)

Inductive sₛ : Set :=
| eₛ
| pₛ
| fₛ (α β : sₛ).

(** A temporary fill in for semantics *)

Inductive meaning : lₗ → mₘ → sₛ → Prop :=
| meaning₁ : ∀ l m, l = ñeneₗ → m = baseₘ → meaning l m eₛ.

Definition spₛₚ := (ϕ * τ * sₛ).

(** A relation for providing proofs of lexical meanings *)

Definition ruleₛₚ (m : mₘ) (k : kₖ) (t : τ) (s : sₛ) :=
  λ (α : mpₘₚ)
    (l : lₗ)
    (mp : MPₘₚ α l)
    (proofₘ : (fst α) ≤ₘ m)
    (proofₖ : fₗₖ l ≤ₖ k)
    (proofₛ : meaning l (fst α) s), (η (snd α), t, s).

(** The above is a constructor for a mapping rule between form entries
and sign entries *)

Inductive SPₛₚ : spₛₚ → lₗ → Prop :=
| simp_adjₛₚ : ∀ α l mp proofₘ proofₖ proofₛ,
    SPₛₚ ((ruleₛₚ baseₘ adjₖ (N ⊸ N) (fₛ eₛ pₛ)) α l mp proofₘ proofₖ proofₛ) l.

(** A SPₛₚ is essentially a well-formed lexical sign plus a lexeme
reference used to simplify the identification of paradigms. For now,
I'll leave the type with only one constructor. *)

Inductive Pₛₚ : spₛₚ → spₛₚ → Prop :=
| inₛₚ : ∀ α β l, SPₛₚ α l → SPₛₚ β l → Pₛₚ α β
| reflₛₚ : ∀ α l, SPₛₚ α l → Pₛₚ α α
| transₛₚ : ∀ α β γ, Pₛₚ α β → Pₛₚ β γ → Pₛₚ α γ
| symₛₚ : ∀ α β, Pₛₚ α β -> Pₛₚ β α.

(** A sign paradigm is an equivalence class. *)

