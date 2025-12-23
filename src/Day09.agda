module Day09 where

open import IO
open import Function
open import Data.Char using (_==_)
open import Data.List using (List; _∷_; []; map; catMaybes; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; _∸_; _*_; _⊓′_; _⊔′_)
open import Data.Nat.Properties using (≤-totalOrder)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; lines; wordsByᵇ)

open import Data.List.Extrema ≤-totalOrder using (max)

parse : String → List (ℕ × ℕ)
parse = catMaybes ∘ map parsePoint ∘ lines
  where
    buildPoint : List (Maybe ℕ) → Maybe (ℕ × ℕ)
    buildPoint (just x ∷ just y ∷ []) = just (x , y)
    buildPoint _ = nothing

    parsePoint : String → Maybe (ℕ × ℕ)
    parsePoint = buildPoint ∘ map (readMaybe 10) ∘ wordsByᵇ (',' ==_)

subsets : ∀ {A : Set} → List A → List (A × A)
subsets [] = []
subsets (x ∷ xs) = map (x ,_) xs ++ subsets xs


part1 : List (ℕ × ℕ) → ℕ
part1 = max zero ∘ map dist ∘ subsets
  where
    diff : ℕ → ℕ → ℕ
    diff x y = (suc (x ⊔′ y)) ∸ (x ⊓′ y)

    dist : ((ℕ × ℕ) × (ℕ × ℕ)) → ℕ
    dist ((x₁ , y₁) , (x₂ , y₂)) = (diff x₁ x₂) * (diff y₁ y₂)

-- part2 : List (ℕ × ℕ) → ℕ
-- part2 = ?

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day09.txt"
  let points = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 points

  putStrLn "Part 2:"
  -- putStrLn ∘ show $ part2 banks
