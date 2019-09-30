# What is Decidable about Gradual Types?
This artifact is for out POPL 2020 submission.

------------

### Step 0: Dependencies
- Stack
Install via this link: https://docs.haskellstack.org/en/stable/install_and_upgrade/
- criterion-1.5.6.1
Install by running the following command:
`stack install criterion-1.5.6.1`

### Step 1: GitHub repository
- Clone this repository:  https://github.com/migeed-z/Maximal-Migration 

This creates a root directory called Maximal-Migration in your current working directory.

### Step 3: Figure 4 results
- Go to the root directory and run:
`stack test/Test.hs`

First, we want to verify the results which appear in Figure 4 in the paper. The figure summerizes four kinds of checks on 12 benchmarks.

When running the above command, you will see the output for each of the four checks on the 12 benchmarks in Figure 4. Below is some sample output. We only show here the first three benchmarks for each check, but the command will show the program and the corresponding results for each benchmark. In all the results below, True corresponds to ✔ and False corresponds to ✕. The benchmarks will appear in the same order they appear in the paper.

------------
**Singleton check**
sees that λx : * . x (succ x) is singleton? = True
  sees that λx : * . x (succ (x True)) is singleton? = False
  sees that λx : * . + (x 4) (x True) is singleton? = False

------------
**Top choice check**
 sees that λx : * . x (succ x) has a top choice? =  True
  sees that λx : * . x (succ (x True)) has a top choice? =  True
  sees that λx : * . + (x 4) (x True) has a top choice? =  True



------------

**Finitness check**
   sees that λx : * . x (succ x) is finite? = True
  sees that λx : * . x (succ (x True)) is finite? = True
  sees that λx : * . + (x 4) (x True) is finite? = True

------------
**Maximality check
**
 sees that λx : * . x (succ x) has max? = True
  sees that λx : * . x (succ (x True)) has max? = True
  sees that λx : * . + (x 4) (x True) has max? = True

### Step 4: Figure 6 results
We now verify the results in Figure 6. We will see text that says: Show migrations (fig 6), which displays the actual migration for each figure in the table if it exists, and outputs Nothing otherwise. Here is a sample output:

------------


**Show migrations (fig 6)**
  sees that λx : * . x (succ x) has a maximal migration Just (λx : * . x (succ x))
  sees that λx : * . x (succ (x True)) has a maximal migration Just (λx : * -> int . x (succ (x True)))

------------
For the first ten benchmarks, we explore the lattice upto the level given by a formula which can be seen in the implementation of findAllMaximalMigrations in `src/Maximality.hs`. This function typically calculates a large level for each program which maybe infeasable for larger programs. For this reason, we have seperated the last three benchmarks into their own test where we run the maximality algorithm upto level 3 only. There is also a fourth benchmark which is the UNSAT NPHard example mentioned in section 7 if the paper.

The check should print "Nothing" for all four benchmarks since none of them have a maximal migration. Here is a sample output:

------------


**Show migrations (fig 6) Large prog**
  sees that (λx : * . λy : * . y (x (λa : * . a)) (x (λb : * . λc : * . b))) (λd : * . d d) has a maximal migration Nothing


------------

Finally, you will notice that for the program
λx : * . λy : * . y x x, 
the maximal migration given by the tool  is 
λx : * . λy : int -> bool -> int . y x x

This is because the function we use in this test finds the *closest* maximal in the lattice. To see that the migration in the table is indeed a valid migration, you can see the output:

------------


**find specific maximal migration
**
sees that λx : int . λy : int -> int -> int . y x x is a maximal migration for λx : * . λy : * . y x x
  should handle x

------------

Here, we run the migration algorithm upto level 5 and collect all maximal migrations and check that the migration shown in the table is valid.


------------

### Step 5: Exploring the lattice
To run the maximality algorithm upto a given lattice, uncomment the line of code that says 
`    -- test_mult_migrate` in `test/Test.hs` then rerun the command:
` stack test/Test.hs`

In Test.hs, go to the line of code that says `test_mult_migrate :: Spec`
where you will see a sample test:
`    example 3 lam [lam1, lam2]
`
This means, run the program lam upto level 3 of the lattice and output the maximal migrations. [lam1, lam2] are the maximal migrations for this program. 

When you run this test, the following output will be displayed:

  sees that at level 3 λx : * . (λy : * . x) x x has migrations [λx : * . (λy : int . x) x x,λx : * . (λy : bool . x) x x]

All sample programs to run tests on can be found in` src/Examples.hs `. 

### Step 7: NP Hardness examples
We want to verify that the NP hardness example seen in section 6.3 has a maximal migration. 

For this, read the part of the output which says:
NP hard example.
Below that line, you will see the proram and the corresponding maximal migration. For this, we have implemented a mapping function *make_mapping* in `NPHard.hs` which takes boolean formulas to programs. 

### Step 8: Performance

To run the performance tests in Figure 5, run the command:

`stack test/Performance.hs `

You can also generate an html report with 
regression tests and time density tests for each benchmark and each check by running the command  

`stack test/Performance.hs --output Report.html`

In both cases, the following will be displayed on the screen:

> benchmarking Singleton /1
time                 319.9 ns   (317.3 ns .. 323.6 ns)
                     0.999 R²   (0.999 R² .. 0.999 R²)
mean                 327.4 ns   (324.7 ns .. 330.1 ns)
std dev              9.265 ns   (7.906 ns .. 10.93 ns)
variance introduced by outliers: 41% (moderately inflated)

This means we are running the Singleton check on the benchmark 1. We can see the mean, std dev. and other statistics. All benchmarks are marked 1 to 12 for each of our checks. They will all run in turn on all benchmarks.

Performance tests are seperated into groups. Let us identify these groups.
- Singleton
Runs all singleton checks on our 12 benchmarks

- Finiteness
Runs finiteness checks on the first 9 (smaller) benchmarks

- FLarge
Runs finiteness checks on the last 3 (large) benchmarks

- TopChoice
Runs topchoice checks on the first 9 (smaller) benchmarks

- TCLarge
Runs topchoice checks on the last 3 (large) benchmarks

- Maximality
Runs maximality checks on the first 9 (smaller) benchmarks upto level 5 of the lattice

- MLarge
Runs maximality checks on the last 3 (larger) benchmarks upto level 3 of the lattice

- MappingSAT
Measures the maximality check on the NPhardness SAT program

- MappingUNSAT
Measures the maximality check on the NPhardness UNSAT program

You can run each group individually to see the performance and generate a seperate html report. A report also lets you see how many times each benchmark was run.

To run a seperate group, use this command:

`stack test/Performance.hs --output report.html groupName`

Without report:
`stack test/Performance.hs  groupName`

For the group MLarge, we recommend running it for a longer time to ensure that each benchmark runs at least 100 times. For this, use the command

`stack test/Performance.hs --output report.html -L 1000 MLarge`


