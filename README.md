# Advent of Code 2025

This repository contains my solutions to the [Advent of Code 2025](https://adventofcode.com/2025) challenges, implemented in [Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php).

## About

Advent of Code is an annual event featuring daily programming puzzles throughout December. This project uses Agda, a dependently typed functional programming language, to solve these challenges.

## Prerequisites

- [Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html) compiler installed on your system
- [Agda standard library](https://github.com/agda/agda-stdlib) installed and configured

## Project Structure

```
.
├── src/           # Agda source files for each day's solution
├── inputs/        # Input files for each day's puzzle
└── out/           # Compiled output (generated)
```

## Running Solutions

To run a solution for a specific day:

1. **Prepare the input file**: Place your puzzle input in the `inputs/` directory with the naming convention `dayXX.txt`. For example, for Day 1:
   ```
   inputs/day01.txt
   ```

2. **Compile and run**: Use the following command to compile and execute the solution:
   ```bash
   agda --compile src/Day01.agda --compile-dir=./out && ./out/Day01
   ```

### Example

For Day 1:
```bash
# Ensure your input is at inputs/day01.txt
agda --compile src/Day01.agda --compile-dir=./out && ./out/Day01
```

For Day 2:
```bash
# Ensure your input is at inputs/day02.txt
agda --compile src/Day02.agda --compile-dir=./out && ./out/Day02
```

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
