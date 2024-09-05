# CAS706-F2024
Repository for Fall 2024 version of CAS 706

## The Book
This is based on [PLFA](https://github.com/plfa/plfa.github.io) and borrows substantially from [Prabhakar Ragde's](https://cs.uwaterloo.ca/~plragde/) course [CS 747](https://cs.uwaterloo.ca/~plragde/747/) which is an 'instance' of PLFA.
Note that current PLFA does not quite work (yet) with the latest Agda. To get
a version that does, instead use [my fork](https://github.com/JacquesCarette/plfa.github.io) and pick branch 'feature-v2.7'.

## This Repo

You will find
- in `handout`, the files used for CAS 706
- in `filled`, what we ended up doing during lectures
- in `CAS706/Exercises`, the assignments.

More material will get posted here as it arises. Such as what was covered in
the lectures, the extra material used, the assignments, etc.

Note that the *Exercises* assume that everything that was done in class,
i.e. the up-to-date content of 'filled' is accessible.

## Getting Agda

The instructions on the [Getting Started](https://plfa.github.io/GettingStarted/) page
are *almost* right...  You should use `Agda-2.7.0` instead of `Agda-2.6.3`
and instead of using the sub-module for the standard library, just use
the normal method for [installing stdlib](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md). Yes, it is a bit fidly.

Please help each other with the Agda installation. It's pure technology,
there is little to be learned by wasting a lot of your time on figuring out
these arcane details!
