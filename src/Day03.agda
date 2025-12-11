module Day03 where

open import IO
open import Function
open import Data.Bool using (not)
open import Data.Char using (toℕ)
open import Data.Nat using (ℕ; suc; zero; _≡ᵇ_; _+_; _∸_; _*_; _^_)
open import Data.Nat.ListAction using (sum)
open import Data.Nat.Show using (show)
open import Data.List using (List; reverse; drop; _∷_; []; dropWhileᵇ; map)
open import Data.String using (String; lines; toList)

import Data.Nat.Properties as NatProps
import Data.List.Extrema NatProps.≤-totalOrder as Extrema

removeLastN : {A : Set} → ℕ → List A → List A
removeLastN n = reverse ∘ drop n ∘ reverse

parse : String → List (List ℕ)
parse = map (map ((_∸ 48) ∘ toℕ) ∘ toList) ∘ lines

getMaxInList : List ℕ → ℕ
getMaxInList = Extrema.max zero

removeUntilNum : List ℕ → ℕ → List ℕ
removeUntilNum xs n with dropWhileᵇ (not ∘ (n ≡ᵇ_)) xs
... | [] = []
... | y ∷ ys = ys

maxJotageInBank : ℕ → List ℕ → ℕ
maxJotageInBank zero bank = getMaxInList bank
maxJotageInBank (suc n) bank =
  let firstBattery = getMaxInList (removeLastN (suc n) bank)
      restBank = removeUntilNum bank firstBattery
      otherBatteries = maxJotageInBank n restBank
  in (firstBattery * 10 ^ (suc n)) + otherBatteries

part1 : List (List ℕ) → ℕ
part1 = sum ∘ map (maxJotageInBank 1)

part2 : List (List ℕ) → ℕ
part2 = sum ∘ map (maxJotageInBank 11)

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day03.txt"
  let banks = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 banks

  putStrLn "Part 2:"
  putStrLn ∘ show $ part2 banks
