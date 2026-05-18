-- All in term mode, for fun

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
  -- | _ :: _, [] => product_nil_right ▸ product_nil_right (as := map f _) ▸ rfl
  | _ :: _ =>
    -- product_eq ▸ Eq.symm product_eq ▸ map_flatMap ▸ Eq.symm flatMap_map \t sorry
    by simp [product, map_flatMap, flatMap_map]; rfl -- TODO

theorem map_product' {as : List α} {bs : List β} {f : (α × β) → γ} :
  (as.product bs).map f = (as.map (Function.curry f)|>.product bs).map fun (f, b) => f b :=
  sorry

end List

inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arrow : Finite → Finite → Finite

namespace Finite

abbrev asType : Finite → Type
  | .unit => Unit
  | .bool => Bool
  | .pair l r => l.asType × r.asType
  | .arrow src dst => src.asType → dst.asType

instance {t : Finite} : Inhabited t.asType :=
  ⟨go t⟩
where
  go : (t : Finite) → t.asType
    | .unit => default
    | .bool => default
    | .pair l r => (go l, go r)
    | .arrow _ dst => fun _ => go dst

def enumerateArrow {α β : Type} (as : List α) (bs : List β) (beq : α → α → Bool) : List (α → β) :=
  as.foldr (init := match bs with | [] => [] | b :: _ => [fun _ => b]) -- note this `init` is not correct if `as = []`
    fun a acc =>
      (acc.product bs).map fun (oldFn, b) =>
        fun a' =>
          if beq a a' then b else oldFn a'

mutual
def beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .unit => true
  | .bool => x == y
  | .pair l r =>
    -- Two pairs are equal iff their parts are respectively equal
    beq l x.fst y.fst && beq r x.snd y.snd
  | .arrow src dst =>
    -- Two functions are equal iff they agree on all inputs
    (enumerate src).all fun inp => beq dst (x inp) (y inp)

/-- All elements of `t.asType` -/
def enumerate : (t : Finite) → List t.asType
  | .unit => [()]
  | .bool => [true, false]
  | .pair l r => List.product (enumerate l) (enumerate r)
  | .arrow tα tβ => enumerateArrow (enumerate tα) (enumerate tβ) (beq tα)
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

theorem enumerate_ne_nil : enumerate t ≠ [] :=
  match t with
  | .unit | .bool => List.cons_ne_nil _ _
  | .pair _ _ => List.product_ne_nil enumerate_ne_nil enumerate_ne_nil
  | .arrow _ _ => enumerateArrow_ne_nil enumerate_ne_nil

theorem beq_refl : beq t x x = true :=
  match t with
  | .unit => rfl
  | .bool => match x with | true | false => rfl
  | .pair _ _ => Bool.and_eq_true_iff.mpr ⟨beq_refl, beq_refl⟩
  | .arrow _ _ => List.all_eq_true.mpr fun _ _ => beq_refl

abbrev _root_.Complete (l : List α) : Prop :=
  ∀ a, a ∈ l

section

-- theorem enumerateArrow_bij_left {as : List α} {bs : List β} (f : α → α') {eq : α → α → Bool} (hf : Functio)
    -- enumerateArrow (as.map f) bs eq' = enumerateArrow as bs eq

-- theorem enumerateArrow_map_right {as : List α} {bs : List β} (f : β → β') {eq : α → α → Bool} :
--     enumerateArrow as (bs.map f) eq = (enumerateArrow as bs eq).map (f ∘ ·) :=
--   match as with
--   | [] => match bs with | [] | _ :: _ => rfl
--   | a :: as' => by
--     simp only [enumerateArrow_cons, List.map_map]
--     rw [enumerateArrow_map_right, ←List.map_product]
--     rw [List.map_map]
--     unfold Prod.map
--     unfold Function.comp
--     dsimp
--     congr 1
--     funext (f', b) a'
--     match eq a a' with | true => rfl | false => rfl
--     -- TODO: cleanup

theorem enumerateArrow_mem_attach_mp {as : List α} {bs : List β} {eq : α → α → Bool} (ha : Complete as):
    ∀ (f : α → β), (f ·.1) ∈ enumerateArrow as.attach bs (eq · ·) → f ∈ enumerateArrow as bs eq := by
  -- TODO lmao clean this up
  unfold enumerateArrow
  simp
  intro f h
  let r : List ({ x // x ∈ as } → β) → List (α → β) → Prop :=
    fun l' l => ∀ f, (f ·.1) ∈ l' → f ∈ l

  have h' := @List.foldr_subtype α (β := List ({ x // x ∈ as } → β)) (p := (· ∈ as)) (as.attach) (fun a acc => List.map (fun x a' => if eq a.val a'.val = true then x.snd else x.fst a') (acc.product bs))
      (fun a acc => List.map (fun x a' => if eq a a'.val then x.snd else x.fst a') (acc.product bs))
  rw [h' (by simp), List.unattach_attach] at h
  -- show r _ _
  -- rw [List.foldr_attach (f := (fun a acc => List.map (fun (f', b) a' => if eq a a'.val = true then b else f' a') (acc.product bs)))] at h
  --  (r := r)

  revert h
  -- apply List.foldr_rel
  revert f
  show r _ _
  apply List.foldr_rel
  · intro f
    match bs with
    | [] => simp
    | _ :: _ => simp; intro h; funext a; have := congrFun h ⟨a, ha a⟩; simp [this]
  · intro a _ fs' fs h
    -- simp
    -- have : (fs'.product bs).map (fun (f, b) (a' : { x // x ∈ as }) => if eq a a'.val then b else f a')
    --      = (fs.product bs).map  (fun (f, b) (a' : _)               => if eq a a'.val then b else f a') :=

    --   have := h sorry
    --   sorry
    intro f hf
    rw [List.mem_map] at ⊢ hf
    have ⟨(f', b), hmem, heq'⟩ := hf

    have ⟨hf', hb⟩ := List.mem_product.mp hmem
    exists ((f' ⟨·, ha _⟩), b)
    rewrite [List.mem_product]
    simp at heq'
    have heq'' : f = fun a' => if eq a a' then b else f' ⟨a', ha a'⟩ := by
      funext a'
      let a'' := Subtype.mk a' (ha a')
      have : a' = a''.val := rfl
      rw [this, ←congrFun heq' a'']
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply h
      simp
      exact hf'
    · assumption
    · funext a'
      let a'' : {a // a ∈ as} := ⟨a', ha a'⟩
      rw [heq'']

--   match as with
--   | [] =>
--     match bs with
--     | [] => simp [enumerateArrow] at h
--     | _ :: _ => exact List.mem_singleton.mpr <| funext fun a => nomatch (ha a)
--   | a :: as' =>
--     simp [enumerateArrow_cons]
--     exists f, f a
--     rw [List.mem_product]
--     refine ⟨⟨?_, ?_⟩, ?_⟩
--     · have := enumerateArrow_mem_attach_mp (as := as'.attach) (eq := (eq · ·)) (by simp_all) as'.mem_attach hb (f ·)
--       sorry
--     · apply hb
--     · funext a <;> simp_all
-- termination_by as.length

theorem enumerateArrow_complete {α β} (as : List α) {bs : List β} (hb : bs ≠ []) {eq : α → α → Bool} (heq : ∀ a a', eq a a' = true ↔ a = a')
    (ha : Complete as) (hb' : Complete bs)
    :
    Complete (enumerateArrow as bs eq) :=
  match as with
  | [] => match bs with | b :: bs' => fun f =>
    List.mem_singleton.mpr <| funext fun a => nomatch (ha a)
    --List.attach_nil ▸ List.mem_singleton.mpr (funext nofun)
  | a :: as' => by
    simp [enumerateArrow_cons, Complete]
    show ∀ f, ∃ f' b', _
    intro f
    exists f, f a
    rw [List.mem_product]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    ·
      have := enumerateArrow_complete as'.attach hb (eq := (eq · ·)) (by simp_all) as'.mem_attach hb' (f ·)
      simp at this
      unfold enumerateArrow at this
      simp at this
      have h' := @List.foldr_subtype α (β := List ({ x // x ∈ as' } → β)) (p := (· ∈ as')) (as'.attach) (fun a acc => List.map (fun x a' => if eq a.val a'.val = true then x.snd else x.fst a') (acc.product bs))
        (fun a acc => List.map (fun x a' => if eq a a'.val then x.snd else x.fst a') (acc.product bs))
      rw [h' (by simp)] at this
      simp at this
      unfold enumerateArrow
      simp

      sorry
      -- rw [List.foldr_subtype (g := fun (a : α) acc => List.map (fun x a' => if eq a a'.val = true then x.snd else x.fst a'))] at this
      -- · sorry
      -- · sorry
      -- · exact fun _ => id
    · apply hb'
    · funext a'
      simp [heq]
      intro ha'; subst a; rfl

termination_by as.length
      --have := enumerateArrow_complete as' (bs := b :: bs') hb (eq := eq) heq
      --simp [enumerateArrow_cons, Complete, List.mem_product] at ⊢ this
      --
      -- intro f
      -- exists f, sorry
      -- refine have h := ?_; ⟨⟨?_, h⟩, h, ?_⟩
      -- · rw [←List.mem_cons]
      --   apply (f _).property
      -- ·
      --   have := this (fun ⟨x, hx⟩ => f ⟨x, by simp [hx]⟩)
      --   simp at this
      --   simp [List.map_attach_eq_pmap]
      --   -- rw [List.attach, List.attachWith, List.map_pmap]
      --   -- rw [List.attach, List.attachWith, List.map_pmap]

      --   sorry
      -- · funext; simp_all

  -- match as, bs with
  -- | a :: as', [] => fun f => nomatch (f ⟨a, List.mem_cons_self⟩)
  -- | a :: as', b :: bs' => fun f => by
  --   have := enumerateArrow_complete (a :: as') ha bs' eq f
  --   simp only [List.attach_cons, enumerateArrow_cons, List.mem_map]
  --   simp
  --   sorry

end

mutual

theorem eq_of_beq_eq_true (h : beq t x y = true) : x = y :=
  match t with
  | .unit => rfl
  | .bool => LawfulBEq.eq_of_beq h
  | .pair _ _ =>
    have ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
    Prod.mk.injEq .. ▸ ⟨eq_of_beq_eq_true h₁, eq_of_beq_eq_true h₂⟩
  | .arrow _ _ =>
    funext fun arg =>
      eq_of_beq_eq_true <|
        List.all_eq_true.mp h arg (enumerate_complete arg)

theorem enumerate_complete : Complete (enumerate t) :=
  match t with
  | .unit => fun () => List.mem_singleton_self ()
  | .bool => fun
    | true => List.mem_cons_self
    | false => List.mem_cons_of_mem true (List.mem_singleton_self false)
  | .pair _ _ => fun (y₁, y₂) =>
    List.mem_product.mpr ⟨enumerate_complete y₁, enumerate_complete y₂⟩
  | .arrow tα tβ => sorry
end

instance {t : Finite} : LawfulBEq t.asType where
  rfl := beq_refl
  eq_of_beq := eq_of_beq_eq_true
#check List.recOn
