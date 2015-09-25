{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE UnicodeSyntax         #-}

-- TODO:
--  * Fix all comments (grep for "docstring")
--  * Write example usage

-- | Extensible variants for small-pass compilation.
--   Based on the work in "Variations on Variants" by J. Garret Morris
--   <http://homepages.inf.ed.ac.uk/jmorri14/pubs/morris-haskell15-variants.pdf>
module Variants ( Fix (..)
                , (:⊕:), (:⊘:)
                , Σ1, Σ2, Σ3, Σ4
                , (▽), inj
                ) where


--------------------------------------------------------------------------------
-------------------------------- Exposed values --------------------------------
--------------------------------------------------------------------------------


-- Note: whenever you see a type variable of the form φ1,
--       it should probably be denoted φ₁ for readability,
--       but this currently breaks HLint and other HSE-based
--       tools.

-- | Type-level fixed point
data Fix ε = In (ε (Fix ε))

-- | Type-level coproduct
data (φ1 :⊕: φ2) ε = InL (φ1 ε) | InR (φ2 ε)

-- | Type-level subtraction
--
--   We use "⊘" instead of "⊖" here because it is easier to visually distinguish
--   from "⊕" at small font sizes.
type family (φ1 :⊘: φ2) where
  φ1          :⊘: φ1 = N
  (φ1 :⊕: φ2) :⊘: φ1 = OnL φ2
  (φ1 :⊕: φ2) :⊘: φ2 = OnR φ1
  (φ1 :⊕: φ2) :⊘: φ3 = IfM φ2 (φ1 :⊘: φ3) (φ1 :∈: φ2)
                           φ1 (φ2 :⊘: φ3) (φ1 :∈: φ3)
  φ1          :⊘: φ2 = Found


-- | Convenient for writing coproducts of multiple types
type Σ1 ε1          κ = ε1                      :⊕: κ
type Σ2 ε1 ε2       κ = ε1 :⊕: ε2               :⊕: κ
type Σ3 ε1 ε2 ε3    κ = ε1 :⊕: ε2 :⊕: ε3        :⊕: κ
type Σ4 ε1 ε2 ε3 ε4 κ = ε1 :⊕: ε2 :⊕: ε3 :⊕: ε4 :⊕: κ

-- | Something about injectivity ... docstring
inj ∷ ∀ φ1 φ2 ε . (Inj φ1 φ2 (φ1 :↠: φ2)) ⇒ φ1 ε → φ2 ε
inj = injP (undefined ∷ φ1 :↠: φ2)


--------------------------------------------------------------------------------
------------------------------- Unexposed values -------------------------------
--------------------------------------------------------------------------------


-- Yes and no ... docstring
data Y
data N

-- docstring
(▽) ∷ (φ1 ε  → α) → (φ2 ε → α) → (φ1 :⊕: φ2) ε → α
(f ▽ _) (InL x) = f x
(_ ▽ g) (InR x) = g x

-- docstring
type family IsIn φ1 φ2 where
  IsIn φ1 φ1          = Y
  IsIn φ1 (φ2 :⊕: φ3) = Or (IsIn φ1 φ2) (IsIn φ1 φ3)
  IsIn φ1 φ2          = Y

-- docstring
type ε1 :∈: ε2 = IsIn ε1 ε2

-- docstring
type family Or α β where
  Or N N = N
  Or α β = Y

-- Refl, like in proofs ... docstring
data Refl

-- Left and right ... docstring
data L α
data R α

-- docstring
-- γ = leftP, ς = inLeft, δ = rightP, τ = inRight
type family IfInj γ τ δ ς where
  IfInj N τ N ς = N
  IfInj N τ δ N = R δ
  IfInj γ N δ ς = L γ
  IfInj γ τ δ ς = N

-- "Into" type family ... docstring
type family φ1 :↠: φ2 where
  φ1 :↠: φ1          = Refl
  φ1 :↠: (φ2 :⊕: φ3) = IfInj (φ1 :↠: φ2) (IsIn φ1 φ3)
                             (φ1 :↠: φ3) (IsIn φ1 φ2)
  φ1 :↠: φ2          = N

-- Typeclass for injective functions ... docstring
class Inj φ1 φ2 π where
  injP ∷ π → φ1 ε → φ2 ε

-- Trivial instance for 'Inj' ... docstring
instance Inj φ φ Refl where
  injP _ = id

-- Instance for left ... docstring
instance Inj φ1 φ2 π ⇒ Inj φ1 (φ2 :⊕: φ3) (L π) where
  injP (_ ∷ L π) = InL . injP (undefined ∷ π)

-- Instance for right ... docstring
instance Inj φ1 φ3 π ⇒ Inj φ1 (φ2 :⊕: φ3) (R π) where
  injP (_ ∷ R π) = InR . injP (undefined ∷ π)

-- docstring
-- In case it's unclear, with -XUnicodeSyntax, ★ is the point kind.
data OnL (φ ∷ ★ → ★)
data OnR (φ ∷ ★ → ★)
data Le  (φ ∷ ★ → ★) π
data Ri  (φ ∷ ★ → ★) π
data Found

-- docstring
type family IfM φ2 γ τ φ1 δ ς where
  IfM φ2 N τ φ1 N ς = N
  IfM φ2 N τ φ1 δ N = OnR φ1
  IfM φ2 γ N φ1 δ ς = OnL φ2

-- docstring
type family OutOf π where
  OutOf (OnL α)  = α
  OutOf (OnR α)  = α
  OutOf (Le φ π) = OutOf π :⊕: φ
  OutOf (Ri φ π) = φ :⊕: OutOf π
