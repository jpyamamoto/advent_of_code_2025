module Day11 where

open import IO
open import Function
open import Data.Char using (_==_)
open import Data.List using (List; _∷_; []; map; drop; take; foldl)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe)
open import Data.Nat using (ℕ; suc; zero; _*_; _+_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String; lines; wordsByᵇ; toList; fromList; _≟_; _++_)
                        renaming (_==_ to _=?_)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Tree.AVL.Map (<-strictTotalOrder-≈)
  using (Map; empty; lookup; insert)
  renaming (fromList to mapFromList)
open import Relation.Nullary.Decidable using (yes; no)

parseDevice : String → String × (List String)
parseDevice s = let xs = toList s
                    id = fromList (take 3 xs)
                    rest = fromList (drop 5 xs)
                    ids = wordsByᵇ (' ' ==_) rest
                in id , ids

parse : String → Map (List String)
parse = mapFromList ∘ map parseDevice ∘ lines

{-# TERMINATING #-} 
countPaths : Map (List String) → String → String → Map ℕ → ℕ × Map ℕ
countPaths adjacencies from to cache with from ≟ to
... | yes _ = 1 , cache
... | no _  with lookup cache from
... | just x = x , cache
... | nothing = case foldl goCount (0 , cache) (fromMaybe [] (lookup adjacencies from)) of
      λ where (result , cache′) → result , insert from result cache′
  where
    goCount : (ℕ × Map ℕ) → String → (ℕ × Map ℕ)
    goCount (acc , cache′) neighbor = 
      case countPaths adjacencies neighbor to cache′ of 
        λ where (count , cache′′) → acc + count , cache′′

numPaths : Map (List String) → String → String → ℕ
numPaths neighs from to = proj₁ $ countPaths neighs from to empty

part1 : Map (List String) → ℕ
part1 neighs = numPaths neighs "you" "out"

part2 : Map (List String) → ℕ
part2 neighs = let toFFT = numPaths neighs "svr" "fft"
                   fftToDAC = numPaths neighs "fft" "dac"
                   dacToOut = numPaths neighs "dac" "out"
               in (toFFT * fftToDAC * dacToOut)

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day11.txt"
  let devices = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 devices

  putStrLn "Part 2:"
  putStrLn ∘ show $ part2 devices
