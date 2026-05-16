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


-- Given A := {x, y} and B := {1, 2, 3}, how do I create the set of all functions from A → B?
-- From ∅ to B, there is one function
-- From {x} to B, there are three functions, {x ↦ 1, x ↦ 2, x ↦ 3}
-- Adding y, we now have 9 functions, with the input being used to switch between elements of B:
-- { x ↦ 1 | y ↦ 1, x ↦ 1 | y ↦ 2, x ↦ 1 | y ↦ 3,
--   x ↦ 2 | y ↦ 1, x ↦ 2 | y ↦ 2, x ↦ 2 | y ↦ 3,
--   x ↦ 3 | y ↦ 1, x ↦ 3 | y ↦ 2, x ↦ 3 | y ↦ 3 }
-- Can we use this technique to build functions from `Fin`s to `Fin`s?

def test (n m : Nat) : List (Fin n → Fin m) :=
  match n with
  | 0 => [Fin.elim0]
  | k + 1 =>
    let ms := List.finRange m
    let below := test k m
    below.product ms|>.map fun (oldFn, j) =>
      fun i =>
        if h : i = 0 then j   -- we are first
        else oldFn (i.pred h) -- otherwise run `oldFn ⟨↑i - 1, ⋯⟩`

def printFinFn (f : Fin n → Fin m) : String :=
  if n == 0 then "<the eliminator>"
  else
    let strs := List.finRange n|>.map fun i => s!"{i} ↦ {f i}"
    " | ".intercalate strs

abbrev _root_.Complete (l : List α) : Prop :=
  ∀ a, a ∈ l

def test' [DecidableEq α] (as : List α) (bs : List β) : List ({a // a ∈ as} → β) :=
  match as with
  | [] => [fun ⟨_, h⟩ => nomatch h]
  | _ :: as' =>
    let below := test' as' bs
    below.product bs|>.map fun (oldFn, b) =>
      fun ⟨a, _⟩ =>
        -- similar to in `test`
        if ha : a ∈ as' then oldFn ⟨a, ha⟩ -- run `oldFn`
        else b                             -- we are first (the head of the list)
termination_by as.length

-- Note we need `DecidableEq` and `Complete` for the above, which is awkward

-- We can write the above as a fold
def test'' [DecidableEq α] (as : List α) (bs : List β) : List (α → β) :=
  as.foldr (init := match bs with | [] => [] | b :: _ => [fun _ => b])
    fun a acc =>
      (acc.product bs).map fun (oldFn, b) =>
        fun a' => if a = a' then b else oldFn a'

#eval (test 3 2).map printFinFn |> String.intercalate "\n" |> IO.println
#eval
  let : List String := test'' (α := Fin 3) (β := Fin 2) (List.finRange _) (List.finRange _)
        |>.map (fun f (x : Fin _) => f x)
        |>.map printFinFn
  (println! this.length) *>
  println! String.intercalate "\n" this

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
  -- -- Pass in `dstElems` instead of `dst` so that `enumerate dst` isn't computed again and again as we recurse
  -- enumerateFn (t : Finite) {γ : Type} (dstElems : List γ) : List (t.asType → γ) :=
  --   match t with
  --   | .unit => dstElems.map fun y => (fun () => y)
  --   | .bool => (dstElems.product dstElems).map fun (y₁, y₂) => (fun | true => y₁ | false => y₂)
  --   | .pair tα tβ =>
  --     -- To get all `(α × β) → γ`, get all `α → β → γ` and then uncurry each
  --     let curried := enumerateFn tα (enumerateFn tβ dstElems)
  --     curried.map Function.uncurry
  --     -- x^(yz) = (x^y)^z
  --   | .arrow tα tβ =>
  --     -- To get all `(α → β) → γ`, TODO figure out how this works
  --     let as := enumerate tα
  --     -- x^(y^z)
  --     sorry

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
