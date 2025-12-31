module Day12 where

open import IO
open import Function
open import Data.Char using (Char) renaming (_==_ to _=?_)
open import Data.List using
  (List; map; catMaybes; wordsByᵇ; drop; splitAt; length; head; filterᵇ; zip)
open import Data.Maybe using (fromMaybe)
open import Data.Nat using (ℕ; _∸_; _≤ᵇ_; _*_)
open import Data.Nat.ListAction using (sum; product)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product using (_×_; _,_; uncurry; swap; map₂)
open import Data.String using (String; lines; toList; _==_; unlines; linesByᵇ; words)
                        renaming (map to mapStr)

getNums : String → List ℕ
getNums = catMaybes ∘ map (readMaybe 10) ∘ words ∘ mapStr replace
  where
    replace : Char → Char
    replace ':' = ' '
    replace 'x' = ' '
    replace c   = c

parseArea : String → ℕ
parseArea = length ∘ filterᵇ ('#' =?_) ∘ toList

parseRegion : String → ℕ × List ℕ
parseRegion s = let parts = linesByᵇ (':' =?_) s
                    totalArea = product $ getNums (fromMaybe "" $ head parts)
                    quantities = getNums (fromMaybe "" $ head (drop 1 parts))
                in totalArea , quantities

parse : String → List ℕ × List (ℕ × List ℕ)
parse s = let sections = (map unlines ∘ wordsByᵇ ("" ==_) ∘ lines) s
              (areas , regions) = splitAt ((length sections) ∸ 1) sections
          in map parseArea areas , map parseRegion ((lines ∘ fromMaybe "" ∘ head) regions)

part1 : List ℕ → List (ℕ × List ℕ) → ℕ
part1 areas = length ∘ filterᵇ (uncurry _≤ᵇ_) ∘ map (swap ∘ map₂ (sum ∘ map (uncurry _*_) ∘ zip areas))

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day12.txt"
  let (areas , regions) = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 areas regions
