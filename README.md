# ABC_FOL

The ABC system is a domain-independent system for repairing faulty Datalog-like theories by combining three existing techniques: abduction, belief revision and conceptual change. Accordingly, it is named the ABC repair system (ABC). Given an observed assertion and a current theory, abduction adds axioms, or deletes preconditions, which explain that observation by making the corresponding assertion derivable from the expanded theory. Belief revision incorporates a new piece of information which conflicts with the input theory by deleting old axioms. Conceptual change uses the reformation algorithm for blocking unwanted proofs or unblocking wanted proofs. The former two techniques change an axiom as a whole, while reformation changes the language in which the theory is written. These three techniques are complementary. But they have not previously been combined into one system. We align these three techniques in ABC, which is capable of repairing logical theories with better result than each individual technique alone. Datalog is used as the underlying logic of theories in this thesis, but the proposed system has the potential to be adapted to theories in other logics.

## Desciptions of ABC System

This repository contains two implementations of the ABC system, namely ABC_Datalog and ABC_FOL. ABC_Datalog is the original implementation of the ABC system, which is based on Datalog. ABC_FOL is the extension of ABC_Datalog, which is based on First-Order Logic (FOL).  

Please refer to `FOL_ABC_thesis.pdf` for details such as the repair plans.

## Evaluation theories

The folder `evaluation` contains the faulty theories tested in the evaluation in our project. The ones with name *h.pl is a theory with heuristics, while ones with name `*nh.pl` is the corresponding theory without heuristics.  

`example1.pl` through `example5.pl` are the examples used in the thesis for ABC_FOL.

### CogAI2023 example

The theory file for the `eggtimer` example, as discussed in the CogAI2023 workshop, can be found in `evaluation/eggtimer.pl` and `evaluation/eggtimer2.pl`.

## Code structure

The implementations of `ABC_FOL` and `ABC_Datalog` are similar but independent. A corresponding folder in `src` contains the code for each implementation. There is a unified interface for calling the program of each implementation, which is `main.pl`. This is the file to be consulted when running the program.  

## How to run the code

Step1. Prepare the theory input file in another folder placed in the project root directory e.g., any file in folder `evaluation`. It has to include a Datalog theory given by _axiom([...])_, and the preferred structure given by _trueSet([...])_ and _falseSet([...])_. Then one can put the items to protect from being changed in _protect([...])_, and heuristics to apply in _heuristics([...])._ Add the following lines at the top of the theory input file:  

```prolog
:- working_directory(_, '../src').
:-[main].

logic(fol). %Choose between fol and datalog
theoryName(eggtimer). %Provide a name for your theory to identify the output files

```

Step2. In a prolog console, consult the theory input file, for example:

```prolog
1 ?- working_directory(_,'./evaluation theories').
true.

2 ?- [mumh].
true.
```

Step3. Call predicate _abc._ The output files include _abc_..._faultFree.txt_ which contains the repair solutions; _abc_..._record.txt_ which has the log information of ABC's procedure, and _abc_..._repNum.txt_ which is the pruned sub-optimal.
