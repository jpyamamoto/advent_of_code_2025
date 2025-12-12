module Day04 where

open import IO
open import Function
open import Data.Bool using (Bool; false)
open import Data.Char using (_==_; Char)
open import Data.Integer using (ℤ; +_; _+_; -[1+_]) renaming (-_ to ℤ-_)
open import Data.Product
  using (_×_; _,_; proj₁; proj₂; map₁; map₂)
open import Data.Nat using (ℕ; suc; zero; _≤ᵇ_) renaming (_+_ to _+ℕ_)
open import Data.Nat.Show using (show)
open import Data.List
  using (List; partitionᵇ; _∷_; []; filterᵇ; map; zip; upTo; length; concat)
open import Data.String using (String; lines; toList; _++_)

open import Data.Nat.Properties using (<-strictTotalOrder)
open import Data.Product.Relation.Binary.Lex.Strict using (×-strictTotalOrder)

import Data.Tree.AVL.Map (×-strictTotalOrder <-strictTotalOrder <-strictTotalOrder) as Map

-_ : ℕ → ℤ
-_ = ℤ-_ ∘ +_

_∈_ : ∀ {A : Set} → (ℤ × ℤ) → Map.Map A → Bool
(+ row , + col) ∈ grid = Map.member (row , col) grid
(_ , -[1+ _ ]) ∈ _ = false
(-[1+ _ ] , _) ∈ _ = false

count : ∀ {A : Set} → (A → Bool) → List A → ℕ
count p = length ∘ filterᵇ p

adjacents : List (ℤ × ℤ)
adjacents = (- 1 , - 1) ∷ (- 1 , + 0) ∷ (- 1 , + 1) ∷
            (+ 0 , - 1)        ∷        (+ 0 , + 1) ∷
            (+ 1 , - 1) ∷ (+ 1 , + 0) ∷ (+ 1 , + 1) ∷ []

zipWithIndex : {A : Set} → List A → List (ℕ × A)
zipWithIndex xs = zip (upTo (length xs)) xs

parse : String → Map.Map ℕ
parse = Map.fromList ∘ concat ∘ map setCoords ∘ zipWithIndex ∘ map parseLine ∘ lines
  where
    parseLine : String → List (ℕ × Char)
    parseLine = filterᵇ (('@' ==_) ∘ proj₂) ∘ zipWithIndex ∘ toList

    setCoords : (ℕ × List (ℕ × Char)) → List ((ℕ × ℕ) × ℕ)
    setCoords (row , xs) = map (map₁ (row ,_) ∘ map₂ (const 0)) xs

countNeighbours : (ℕ × ℕ) → Map.Map ℕ → ℕ
countNeighbours (y , x) grid = count diff adjacents
  where
    diff : (ℤ × ℤ) → Bool
    diff (yDiff , xDiff) = (+ y + yDiff , + x + xDiff) ∈ grid

convGrid : Map.Map ℕ → Map.Map ℕ
convGrid grid = Map.foldr step Map.empty grid
  where
    step : (ℕ × ℕ) → ℕ → Map.Map ℕ → Map.Map ℕ
    step coord _ newGrid = Map.insert coord (countNeighbours coord grid) newGrid

partitionValid : Map.Map ℕ → (ℕ × Map.Map ℕ)
partitionValid grid =
  let gridList = Map.toList grid
      (toDelete , toKeep) = partitionᵇ ((_≤ᵇ 3) ∘ proj₂) gridList
  in (length toDelete) , (convGrid $ Map.fromList toKeep)

part1 : Map.Map ℕ → ℕ
part1 = proj₁ ∘ partitionValid ∘ convGrid

{-# TERMINATING #-}
part2 : Map.Map ℕ → ℕ
part2 grid with partitionValid (convGrid grid)
... | zero , _ = zero
... | suc n , newGrid = suc n +ℕ part2 newGrid

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day04.txt"
  let grid = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 grid

  putStrLn "Part 2:"
  putStrLn ∘ show $ part2 grid
