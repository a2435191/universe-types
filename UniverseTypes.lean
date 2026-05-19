-- Mostly in term mode, for fun
-- https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/The-Universe-Design-Pattern

namespace List

def product (as : List α) (bs : List β) : List (α × β) :=
  as.flatMap fun a => bs.map (a, ·)

theorem mem_product {as : List α} {bs : List β} : (a, b) ∈ as.product bs ↔ a ∈ as ∧ b ∈ bs := ⟨
  (fun h =>
    have ⟨_, ha', h'⟩ := mem_flatMap.mp h
    have ⟨_, hb', h''⟩ := mem_map.mp h'
    have ⟨ha'_eq, hb'_eq⟩ := Prod.mk.inj h''
    ⟨ha'_eq ▸ ha', hb'_eq ▸ hb'⟩),
  fun ⟨ha, hb⟩ =>
    mem_flatMap_of_mem ha <| mem_map_of_mem hb⟩

theorem product_ne_nil {as : List α} {bs : List β} (ha : as ≠ []) (hb : bs ≠ []) : as.product bs ≠ [] :=
  have ⟨_a, _as', ha'⟩ := ne_nil_iff_exists_cons.mp ha
  have ⟨_b, _bs', hb'⟩ := ne_nil_iff_exists_cons.mp hb
  ha' ▸ hb' ▸ fun h => cons_ne_nil _ _ h

theorem product_eq {as : List α} {bs : List β} :
    as.product bs = as.flatMap fun a => bs.map (a, ·) :=
  rfl

theorem product_nil_left {α β} {bs : List β} : product (α := α) [] bs = [] :=
  rfl

theorem product_nil_right {α β} {as : List α} : product (β := β) as [] = [] :=
  product_eq ▸ flatMap_eq_nil_iff.mpr fun _ _ => rfl

theorem map_product {as : List α} {bs : List β} {f : α → γ} {g : β → δ} :
    (as.product bs).map (Prod.map f g) = product (as.map f) (bs.map g) :=
  match as with
  | [] => rfl
  | _ :: _ =>
    by simp [product, map_flatMap, flatMap_map]; rfl -- TODO

end List

inductive Finite where
  | empty
  | unit
  | bool
  | option : Finite → Finite
  | pair : Finite → Finite → Finite
  | arrow : Finite → Finite → Finite

namespace Finite

abbrev asType : Finite → Type
  | .empty => Empty
  | .unit => Unit
  | .bool => Bool
  | .option t => Option t.asType
  | .pair l r => l.asType × r.asType
  | .arrow src dst => src.asType → dst.asType

-- We need this predicate and the theorem `isEmpty_iff` to construct the vacuous
-- function (like `Empty.elim`) below in `enumerate`. Otherwise we would need some way of getting from
-- `enumerate tα = []` and `enumerate tβ = []` to `α → β`, which would probably involve attaching the completeness
-- theorems to everything, and that would be a pain.
abbrev isEmpty : Finite → Bool
  | .empty => true
  | .unit | .bool | .option _ => false
  | .pair l r => l.isEmpty || r.isEmpty
  | .arrow src dst => !src.isEmpty && dst.isEmpty

theorem isEmpty_iff {t} : isEmpty t = true ↔ (t.asType → False) := by
  rcases t <;> try (simp; done)
  · simp only [asType, true_iff]; nofun
  · rename_i l r
    simp only [Bool.or_eq_true, isEmpty_iff (t := l), isEmpty_iff (t := r), Prod.forall]
    grind
  · rename_i src dst
    simp only [isEmpty, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff]
    simp only [ne_eq, isEmpty_iff, Classical.not_forall, not_false_eq_true]
    constructor
    · intro h f
      have ⟨⟨x, _⟩, hy⟩ := h
      exact hy (f x)
    · intro h
      simp [asType] at h
      refine ⟨?_, fun y => h (fun _ => y)⟩
      -- TODO: I don't think we need Classical here?
      rw [←Classical.not_forall_not]
      intro h'
      exact h fun x => (h' x trivial).elim

-- I enumerate arrow types directly. I find it makes more sense than
-- `Finite.functions` in the original example
/-- Enumerate all functions from `α → β`. Note that if `as = bs = []`,
  returns `[]` instead of the single function from an empty type to an empty type. -/
def enumerateArrow {α β : Type} (as : List α) (bs : List β) (beq : α → α → Bool) : List (α → β) :=
  as.foldr (init := match bs with | [] => [] | b :: _ => [fun _ => b]) -- note this `init` is not correct if `as = bs = []`
    fun a acc =>
      (acc.product bs).map fun (oldFn, b) =>
        fun a' =>
          if beq a a' then b else oldFn a'

mutual
def beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .empty => true -- vacuous
  | .unit => true
  | .bool => x == y
  | .option t =>
    match x, y with
    | .none, .none => true
    | .some x', .some y' => beq t x' y'
    | _, _ => false
  | .pair l r =>
    -- Two pairs are equal iff their parts are respectively equal
    beq l x.fst y.fst && beq r x.snd y.snd
  | .arrow src dst =>
    -- Two functions are equal iff they agree on all inputs
    (enumerate src).all fun inp => beq dst (x inp) (y inp)

/-- All elements of `t.asType` -/
def enumerate : (t : Finite) → List t.asType
  | .empty => []
  | .unit => [()]
  | .bool => [true, false]
  | .option t => .none :: (enumerate t).map some
  | .pair l r => List.product (enumerate l) (enumerate r)
  | .arrow tα tβ =>
    if h : isEmpty tα then
      -- vacuous function
      [fun a => (isEmpty_iff.mp h a).elim]
    -- else if isEmpty tβ then [] -- could include this small optimization
    else enumerateArrow (enumerate tα) (enumerate tβ) (beq tα)
end

instance {t : Finite} : BEq t.asType where
  beq := beq t

#eval beq (.arrow (.pair (.arrow .bool .bool) .bool) .bool) (fun (f, x) => f x) (fun (f, x) => f (not x))

theorem enumerateArrow_cons {as : List α} {bs : List β} {eq : α → α → Bool} {a : α} :
    enumerateArrow (a :: as) bs eq = ((enumerateArrow as bs eq).product bs).map (fun (f, b) a' => if eq a a' then b else f a') :=
  rfl

theorem enumerateArrow_ne_nil (hb : bs ≠ []) : enumerateArrow as bs eq ≠ [] :=
  match as with
  | [] => match bs with | _ :: _ => List.cons_ne_nil _ _
  | _ :: _ => fun hn =>
    have hn := List.map_eq_nil_iff.mp hn
    have := List.product_ne_nil (enumerateArrow_ne_nil hb (eq := eq)) hb
    this hn

theorem beq_refl : beq t x x = true :=
  match t with
  | .empty => rfl
  | .unit => rfl
  | .bool => match x with | true | false => rfl
  | .option t => match x with | none => rfl | some _ => beq_refl (t := t)
  | .pair _ _ => Bool.and_eq_true_iff.mpr ⟨beq_refl, beq_refl⟩
  | .arrow _ _ => List.all_eq_true.mpr fun _ _ => beq_refl

abbrev _root_.Complete (l : List α) : Prop :=
  ∀ a, a ∈ l

section

/-- `enumerateArrow` generates all functions that take inputs from `as` and send them to elements in `bs`.
  What do the functions do with the inputs not in `as`? Send them to the default element in `bs` (the head).  -/
theorem enumerateArrow_mem_lemma (as : List α) (b : β) (bs' : List β) (eq : α → α → Bool) (heq : ∀ a a', eq a a' = true ↔ a = a') (hb : Complete (b :: bs')) :
    ∀ f, (∀ a, a ∈ as ∨ f a = b) → f ∈ enumerateArrow as (b :: bs') eq  := by
  induction as with
  | nil => exact fun f h =>
        List.mem_singleton.mpr <| funext fun a =>
          match h a with
          | .inl h' => nomatch h'
          | .inr h' => h'
  | cons a as' ih =>
    intro f h
    simp only [List.mem_cons, or_assoc] at h
    let f' a' := if eq a a' then b else f a'
    replace ih := ih f'
    have : ∀ (a' : α), a' ∈ as' ∨ f' a' = b :=
      fun a' =>
        match ha' : eq a a' with
        | true => .inr <| by simp [f', ha']
        | false =>
          match h a' with
          | .inl ha'₂ => by symm at ha'₂; rw [←heq] at ha'₂; simp_all
          | .inr h => by unfold f'; simp [ha', h]

    rw [enumerateArrow_cons]
    rw [List.mem_map]
    -- witnesses (f₀, b₀) must satisfy f a = b₀, and for all a' ≠ a, f₀ a' = f a'
    exists (f', f a)
    simp [List.mem_product]

    refine ⟨⟨ih this, List.mem_cons.mp <| hb (f a)⟩, ?_⟩
    funext; split <;> simp_all [f']

theorem enumerateArrow_complete {α β} {as : List α} {bs : List β} (hb : as ≠ [] ∨ bs ≠ []) {eq : α → α → Bool} (heq : ∀ a a', eq a a' = true ↔ a = a')
    (ha : Complete as) (hb' : Complete bs)
    : Complete (enumerateArrow as bs eq) :=
  fun f =>
    match as, bs with
    | a :: _, [] => nomatch hb' (f a)
    | as, b :: bs' => enumerateArrow_mem_lemma as b bs' eq heq hb' f fun a => .inl (ha a)

end


mutual

theorem eq_of_beq_eq_true (h : beq t x y = true) : x = y :=
  match t with
  | .unit => rfl
  | .bool => LawfulBEq.eq_of_beq h
  | .option t =>
    match x, y with
    | .none, .none => rfl
    | .some _, .some _ => congrArg _ (eq_of_beq_eq_true h)
    | .some _, .none | .none, .some _ => (Bool.false_ne_true h).elim
  | .pair _ _ =>
    have ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
    Prod.mk.injEq .. ▸ ⟨eq_of_beq_eq_true h₁, eq_of_beq_eq_true h₂⟩
  | .arrow _ _ =>
    funext fun arg =>
      eq_of_beq_eq_true <|
        List.all_eq_true.mp h arg (enumerate_complete arg)

theorem enumerate_complete : Complete (enumerate t) :=
  match t with
  | .empty => nofun
  | .unit => fun () => List.mem_singleton_self ()
  | .bool => fun
    | true => List.mem_cons_self
    | false => List.mem_cons_of_mem true (List.mem_singleton_self false)
  | .option t => fun
    | .none => List.mem_cons_self
    | .some x => List.mem_cons_of_mem _ <| List.mem_map_of_mem (enumerate_complete x)
  | .pair _ _ => fun (y₁, y₂) =>
    List.mem_product.mpr ⟨enumerate_complete y₁, enumerate_complete y₂⟩
  | .arrow tα tβ => fun f => by -- TODO
    simp only [enumerate]
    split
    · rw [List.mem_singleton]
      funext a
      exact (isEmpty_iff.mp ‹_› a).elim
    · apply enumerateArrow_complete
      · -- simple enough to show `enumerate tα ≠ []`
        rename_i ha
        exact .inl fun hn =>
          ha <| isEmpty_iff.mpr fun a =>
            nomatch hn ▸ enumerate_complete a
      · exact fun _ _ => ⟨eq_of_beq_eq_true, fun h => h ▸ beq_refl⟩
      · apply enumerate_complete
      · apply enumerate_complete

end

#print axioms enumerate_complete

instance {t : Finite} : LawfulBEq t.asType where
  rfl := beq_refl
  eq_of_beq := eq_of_beq_eq_true
