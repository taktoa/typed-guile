{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

-- | Main module for Guile type system
module TypedGuile (main) where

import           TypedGuile.Variants

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
  ENoop ∷  FExpr α ε                             → FExpr α       (ε :⊕: CN)

removeNoop ∷ FExpr α ε → Expr α (ε :⊘: CN)
removeNoop = undefined

main ∷ IO ()
main = return ()
