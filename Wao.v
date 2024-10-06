(** * Wao Tededo Fragment
    
The purpose of this file is to eventually lay out a significant
grammatical fragment of Wao Tededo, beginning with a simple treatment
of adjectival classifiers. It is also a place where I plan to
implement various innovations of the underlying formalism. *)

Require Import Coq.Strings.String.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Lists.List.

Open Scope type_scope.  Open Scope string_scope.

(** The quasi phonological representation of morphological forms use
the string definition from the standard library. *)

Inductive mₘ : Set :=
| baseₘ
| poₘ
| concatₘ : mₘ → mₘ → mₘ.

Infix "⊙" := concatₘ (at level 60, right associativity).

(** mₘ are basic symbols used to form category names. Associated
types, functions and relations will have ₘ in their name. *)

Inductive Mₘ : mₘ → Prop :=
| baseM : Mₘ baseₘ
| poM : Mₘ poₘ.

(** Using mₘ instances, a finite number of category names Mₘ are
licensed. *)

Inductive leₘ : mₘ → mₘ → Prop :=
| reflₘ : ∀ α, Mₘ α → leₘ α α
| transₘ : ∀ α β γ, Mₘ α → Mₘ β → Mₘ γ → leₘ α β → leₘ β γ → leₘ α γ. 

Axiom antisymₘ : ∀ α β : mₘ, leₘ α β → leₘ β α → α = β.

Infix "≤ₘ" := leₘ (at level 60, right associativity).

(** A partial order is defined over mₘ instances, where only Mₘ
instances are ordered. *)

Inductive lₗ : Set :=
| ñeneₗ (* big *)
| giitaₗ. (* small *)

(** Lexemes are defined as a simple inductive type lₗ. The ₗ is used
in names of types, functions and relations associated with lexemes. *)

Inductive kₖ : Set :=
| adjₖ
| anyₖ.

(** kₖ are names of form classes, similar in concept to inflection
classes. The k is for the beginning sound of /klæs/ and like ₘ the ₖ
is used for names of types, functions and relations associated with
kₖ. *)

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

(** Each lexeme has a form class. Hypothetically, this could
eventually be defined as a non-functional relation. Not much hinges on
the functional nature of the relation. *)

Definition poₜ (stem : string) : string :=
  stem ++ "po".
                        
(** poₜ is a simple rule for suffixing the sting "po" to a base. *)

Definition mpₘₚ := (mₘ * string).

(** This type is named with ₘₚ instead of ₘₜ because it stands for
morphological paradigm. *)

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

Inductive stat_term : Set :=
| ent
| prp
| func : stat_term -> stat_term -> stat_term.

Axiom e prop : Set.
Axiom truth falsity : prop.
Axiom p_not : prop -> prop.
Axiom p_and p_or p_implies p_iff : prop -> prop -> prop.
Axiom p_entails : prop -> prop -> Prop.
Definition p_equiv : prop -> prop -> Prop := fun p q : prop => (p_entails p q) /\ (p_entails q p).

Fixpoint Sns (s : stat_term) : Set :=
  match s with
  | ent => e
  | prp => prop
  | func a b => (Sns a) -> (Sns b)
  end.

Infix "AND" := p_and (at level 80).
                     
(** Using Jordan Needle's formalization of Agnostic Hyper-intentional
Semantics. *)

Axiom big : e → prop.

Axiom tall : e → prop.

Axiom small : e → prop.

Axiom boat : e → prop.

Axiom hand : e → prop.

(** sense is a sigma type. s is a stat term and Sns s must be inhabited. *)

Definition sense := { s : stat_term & Sns s}.

Definition lexmeaning : list (lₗ * sense) := 
  cons (ñeneₗ, existT Sns (func ent prp) big)
       (cons (ñeneₗ, existT Sns (func ent prp) tall)
             (cons (giitaₗ, existT Sns (func ent prp) small) nil)).

Definition catmeaning : list (mₘ * sense) :=
  cons (poₘ, existT Sns (func ent prp) boat)
       (cons (poₘ, existT Sns (func ent prp) hand) nil).

Definition conjmeaning (α β : e → prop) : (e → prop) :=
  λ γ,(α γ) AND (β γ).
  
Inductive meaning : sense → lₗ → mₘ → Prop :=
  m₁ : ∀ s l m, m = baseₘ → In (l, s) lexmeaning → meaning s l m
| m₂ : ∀ (s₁ : e → prop) (s₂ : e → prop) l m,
    m = poₘ →
    In (l, existT Sns (func ent prp) s₁) lexmeaning →
    In (m, existT Sns (func ent prp) s₂) catmeaning →
    meaning (existT Sns (func ent prp) (conjmeaning s₁ s₂)) l m.

(** A relation for providing proofs of lexical meanings. This is at
the proof of concept stage. *)

Definition spₛₚ := (ϕ * τ * sense).

(** A type alias for a lexical sign *)

Definition ruleₛₚ (m : mₘ) (k : kₖ) (t : τ) (s : stat_term) :=
  λ (α : mpₘₚ)
    (l : lₗ)
    (mp : MPₘₚ α l)
    (sₗₑₓ : stat_term)
    (β : Sns sₗₑₓ)
    (γ : Sns sₗₑₓ → Sns s)
    (proofₘ : (fst α) ≤ₘ m)
    (proofₖ : fₗₖ l ≤ₖ k)
    (proofₛ : meaning (existT Sns sₗₑₓ β) l (fst α)),
  (η (snd α), t, existT Sns s (γ β)).

(** The above is a constructor for a mapping rule between form entries
and sign entries *)

Definition e₁_identity (x : e → prop) := x.

Inductive SPₛₚ : spₛₚ → lₗ → Prop :=
  simp_adjₛₚ : ∀ α l mp (sₗₑₓ : stat_term) β proofₘ proofₖ proofₛ,
    SPₛₚ ((ruleₛₚ baseₘ adjₖ (N ⊸ N) (func ent prp))
            α l mp (func ent prp) β e₁_identity proofₘ proofₖ proofₛ) l
| po_adjₛₚ : ∀ α l mp (sₗₑₓ : stat_term) β proofₘ proofₖ proofₛ,
    SPₛₚ ((ruleₛₚ poₘ adjₖ (N ⊸ N) (func ent prp))
            α l mp (func ent prp) β e₁_identity proofₘ proofₖ proofₛ) l.

(** A SPₛₚ is a well-formed lexical sign plus a lexeme reference used
to simplify the identification of paradigms. The first constructor is
for basic adjective with no classifier. The second is for an adjective
with a classifier that takes a syntactic argument. *)

Inductive Pₛₚ : spₛₚ → spₛₚ → Prop :=
| inₛₚ : ∀ α β l, SPₛₚ α l → SPₛₚ β l → Pₛₚ α β
| reflₛₚ : ∀ α l, SPₛₚ α l → Pₛₚ α α
| transₛₚ : ∀ α β γ, Pₛₚ α β → Pₛₚ β γ → Pₛₚ α γ
| symₛₚ : ∀ α β, Pₛₚ α β -> Pₛₚ β α.

(** A sign paradigm is an equivalence class. *)

