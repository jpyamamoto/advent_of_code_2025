module Day06 where

open import IO
open import Function
open import Data.Bool using (not)
open import Data.Char using (Char; _==_)
open import Data.List
  using (List; _∷_; []; filterᵇ; map; length; catMaybes; splitAt; zip)
  renaming (wordsByᵇ to chunksByᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _∸_)
open import Data.Nat.ListAction using (sum; product)
open import Data.Nat.Show using (show; readMaybe)
open import Data.Product using (_×_; _,_; map₁)
open import Data.String
  using (String; lines; wordsByᵇ; toList; fromList)
  renaming (_==_ to _=~_)

{-# FOREIGN GHC
  import qualified Data.List as HList
#-}

postulate
  transpose : {A : Set} → List (List A) → List (List A)

{-# COMPILE GHC transpose = \ _ xs -> HList.transpose xs #-}

data Op : Set where
  ⊕ : Op
  ⊗ : Op

record Exercise : Set where
  constructor ex[_,_]
  field
    nums : List ℕ
    op : Op

parseOpsLine : String → List Op
parseOpsLine = catMaybes ∘ map parseOp ∘ toList
  where
    parseOp : Char → Maybe Op
    parseOp '+' = just ⊕
    parseOp '*' = just ⊗
    parseOp _   = nothing

parseNums : List String → List ℕ
parseNums = catMaybes ∘ map (readMaybe 10)

partitionLines : List String → List String × List Op
partitionLines ls with splitAt (length ls ∸ 1) ls
... | rows , opsRow ∷ [] = rows , parseOpsLine opsRow
... | _ , _ = [] , []

parseExercises : List (List ℕ) × List Op → List Exercise
parseExercises (args , ops) = map buildExercise (zip ops args)
  where
    buildExercise : Op × List ℕ → Exercise
    buildExercise (op , args) = ex[ args , op ]

parse : String → List String × List Op
parse = partitionLines ∘ lines

solveExercise : Exercise → ℕ
solveExercise ex[ args , ⊕ ] = sum args
solveExercise ex[ args , ⊗ ] = product args

clean : String → String
clean = fromList ∘ filterᵇ (not ∘ (' ' ==_)) ∘ toList

rotate : List String → List String
rotate = map fromList ∘ transpose ∘ map toList

part1 : List String × List Op → ℕ
part1 = sum ∘ map solveExercise ∘ parseExercises ∘ map₁ createArgs
  where
    createArgs = transpose ∘ map (parseNums ∘ wordsByᵇ (' ' ==_))

part2 : List String × List Op → ℕ
part2 = sum ∘ map solveExercise ∘ parseExercises ∘ map₁ createArgs
  where
    createArgs = map parseNums ∘ chunksByᵇ ("" =~_) ∘ map clean ∘ rotate

main : Main
main = run do
  contents ← readFiniteFile "./inputs/day06.txt"
  let exercises = parse contents

  putStrLn "Part 1:"
  putStrLn ∘ show $ part1 exercises

  putStrLn "Part 2:"
  putStrLn ∘ show $ part2 exercises
