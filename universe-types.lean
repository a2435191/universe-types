-- All in term mode, for fun

def List.product (as : List α) (bs : List β) : List (α × β) :=
  as.flatMap fun a => bs.map (a, ·)

theorem List.mem_product {as : List α} {bs : List β} : (a, b) ∈ as.product bs ↔ a ∈ as ∧ b ∈ bs := ⟨
  (fun h =>
    have ⟨_, ha', h'⟩ := List.mem_flatMap.mp h
    have ⟨_, hb', h''⟩ := List.mem_map.mp h'
    have ⟨ha'_eq, hb'_eq⟩ := Prod.mk.inj h''
    ⟨ha'_eq ▸ ha', hb'_eq ▸ hb'⟩),
  fun ⟨ha, hb⟩ =>
    List.mem_flatMap_of_mem ha <| List.mem_map_of_mem hb⟩

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
  | .arrow tα tβ =>
    let as := enumerate tα
    let bs := enumerate tβ
    as.foldr (init := [fun _ => default])
      fun a acc =>
        (acc.product bs).map fun (oldFn, b) =>
          fun a' =>
            if beq tα a a' then b else oldFn a'
end

instance {t : Finite} : BEq t.asType where
  beq := beq t

-- theorem beq_refl : beq t x x = true :=
--   match t with
--   | .unit => rfl
--   | .bool => match x with | true | false => rfl
--   | .pair _ _ => Bool.and_eq_true_iff.mpr ⟨beq_refl, beq_refl⟩
--   | .fn _ _ => List.all_eq_true.mpr fun _ _ => beq_refl

-- theorem beq.enumerateFn_correct {elts : List α} (h : Complete elts) : Complete (enumerateFn t elts) :=
--   fun f =>
--     match t with
--     | .unit => List.mem_map.mpr ⟨f (), h _, rfl⟩
--     | .bool => List.mem_map.mpr
--       ⟨
--         (f true, f false),
--         List.mem_product.mpr ⟨h _, h _⟩,
--         funext fun | true => rfl | false => rfl⟩
--     | .pair l r => List.mem_map.mpr
--       ⟨
--         Function.curry f,
--         beq.enumerateFn_correct (beq.enumerateFn_correct h) _,
--         Function.uncurry_curry _⟩
--     | .fn src dst => sorry

-- theorem beq.enumerate_correct : Complete (enumerate t) :=
--   match t with
--   | .unit => fun () => List.mem_singleton_self ()
--   | .bool => fun
--     | true => List.mem_cons_self
--     | false => List.mem_cons_of_mem true (List.mem_singleton_self false)
--   | .pair _ _ => fun (y₁, y₂) =>
--       List.mem_product.mpr ⟨beq.enumerate_correct y₁, beq.enumerate_correct y₂⟩
--   | .fn _ _ => beq.enumerateFn_correct beq.enumerate_correct

-- theorem eq_of_beq_eq_true (h : beq t x y) : x = y :=
--   match t with
--   | .unit => rfl
--   | .bool => LawfulBEq.eq_of_beq h
--   | .pair _ _ =>
--     have ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp h
--     Prod.mk.injEq .. ▸ ⟨eq_of_beq_eq_true h₁, eq_of_beq_eq_true h₂⟩
--   | .fn _ _ =>
--     funext fun arg =>
--       eq_of_beq_eq_true <|
--         List.all_eq_true.mp h arg (beq.enumerate_correct arg)

-- instance {t : Finite} : LawfulBEq t.asType where
--   rfl := beq_refl
--   eq_of_beq := eq_of_beq_eq_true
