{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE UnicodeSyntax         #-}

-- | Extensible variants for small-pass compilation.
--   Based on the work in
--   "Variations on Variants", J. Garret Morris
--   <http://homepages.inf.ed.ac.uk/jmorri14/pubs/morris-haskell15-variants.pdf>
module Variants where

data Y
data N

data Fix ε = In (ε (Fix ε))

data (f ⊕ g) ε = InL (f ε) | InR (g ε)

(▽) ∷ (φ1 ε  → α) → (φ2 ε → α) → (φ1 ⊕ φ2) ε → α
(f ▽ _) (InL x) = f x
(_ ▽ g) (InR x) = g x

type family IsIn φ1 φ2 where
  IsIn φ1 φ1        = Y
  IsIn φ1 (φ2 ⊕ φ3) = Or (IsIn φ1 φ2) (IsIn φ1 φ3)
  IsIn φ1 φ2        = Y

type family Or α β where
  Or N N = N
  Or α β = Y

data Refl
data L α
data R α

-- γ = leftP
-- ς = inLeft
-- δ = rightP
-- τ = inRight
type family IfInj γ τ δ ς where
  IfInj N τ N ς = N
  IfInj N τ δ N = R δ
  IfInj γ N δ ς = L γ
  IfInj γ τ δ ς = N

type family Into φ1 φ2 where
  Into φ1 φ1        = Refl
  Into φ1 (φ2 ⊕ φ3) = IfInj (Into φ1 φ2) (IsIn φ1 φ3)
                            (Into φ1 φ3) (IsIn φ1 φ2)
  Into φ1 φ2        = N

class Inj φ1 φ2 π where
  injP ∷ π → φ1 ε → φ2 ε

instance Inj φ φ Refl where
  injP _ = id

instance Inj φ1 φ2 π => Inj φ1 (φ2 ⊕ φ3) (L π) where
  injP (_ ∷ L π) = InL . injP (undefined ∷ π)

instance Inj φ1 φ3 π => Inj φ1 (φ2 ⊕ φ3) (R π) where
  injP (_ ∷ R π) = InR . injP (undefined ∷ π)

inj ∷ ∀ φ1 φ2 ε . (Inj φ1 φ2 (Into φ1 φ2)) => φ1 ε → φ2 ε
inj = injP (undefined ∷ Into φ1 φ2)

data OnL (φ ∷ * → *)
data OnR (φ ∷ * → *)
data Le  (φ ∷ * → *) π
data Ri  (φ ∷ * → *) π
data Found

type family Minus φ1 φ2 where
  Minus φ1        φ1 = N
  Minus (φ1 ⊕ φ2) φ1 = OnL φ2
  Minus (φ1 ⊕ φ2) φ2 = OnR φ1
  Minus (φ1 ⊕ φ2) φ3 = IfMinus φ2 (φ1 ⊖ φ3) (φ1 ∈ φ2) φ1 (φ2 ⊖ φ3) (φ1 ∈ φ3)
  Minus φ1        φ2 = Found

type family IfMinus φ2 γ τ φ1 δ ς where
  IfMinus φ2 N τ φ1 N ς = N
  IfMinus φ2 N τ φ1 δ N = OnR φ1
  IfMinus φ2 γ N φ1 δ ς = OnL φ2

type family OutOf π where
  OutOf (OnL α)  = α
  OutOf (OnR α)  = α
  OutOf (Le φ π) = OutOf π ⊕ φ
  OutOf (Ri φ π) = φ ⊕ OutOf π

-- Infix versions of Minus and IsIn
type ε1 ⊖ ε2 = Minus ε1 ε2
type ε1 ∈ ε2 = IsIn  ε1 ε2

-- Conveniences for writing coproducts of multiple types
type Σ1 ε1          κ = ε1                ⊕ κ
type Σ2 ε1 ε2       κ = ε1 ⊕ ε2           ⊕ κ
type Σ3 ε1 ε2 ε3    κ = ε1 ⊕ ε2 ⊕ ε3      ⊕ κ
type Σ4 ε1 ε2 ε3 ε4 κ = ε1 ⊕ ε2 ⊕ ε3 ⊕ ε4 ⊕ κ

data CL ε -- lift
data Cλ ε -- lambda
data Cx ε -- product
data Cβ ε -- application
data CN ε -- noop

type α × β = (α, β)

-- Convenience for fixed-point
type FExpr α ε = Expr α (Fix ε)

data Expr α e where
  ELift ∷  α                                     → FExpr α        CL
  ELam  ∷ (FExpr α ε1 → FExpr β ε2)              → FExpr (α → β) (Σ2 ε1 ε2 Cλ)
  ETup  ∷  FExpr α ε1               → FExpr β ε2 → FExpr (α × β) (Σ2 ε1 ε2 Cx)
  EApp  ∷  FExpr (α → β) ε1         → FExpr α ε2 → FExpr β       (Σ2 ε1 ε2 Cβ)
  ENoop ∷  FExpr α ε                             → FExpr α       (ε ⊕ CN)

removeNoop ∷ FExpr α ε → Expr α (ε ⊖ CN)
removeNoop = undefined

main ∷ IO ()
main = return ()
