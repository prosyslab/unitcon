+++
date = '2024-09-12'
title = 'Overview'
+++

The overall structure of UnitCon is illustrated below.
![overview of UnitCon](posts/overview.png)

## 1. Initialization
For the given target program location. UnitCon first the error entry methods using the call graph derived by the static analyzer. Then UnitCon generates an initial set of partial test cases each of which calls an error entry methods. Such partial test cases are written in a domain-specific language that we designed for the synthesis.

## 2. Enumeration
Given a set of partial test cases, UnitCon enumerates new partial unit tests by expanding the placeholders.

## 3. Pruning & Prioritization
To improve the efficiency, we guide the search using static analysis results.


### 3.1. Pruning
UnitCon effectively prunes the search space by comparing the semantics between partial test cases. If two partial test cases are deemed to be semantically equivalent by the static analyzer, UnitCon discards the larger one.

     
### 3.2. Prioritization
UnitCon effectively prioritizes the partial test cases that are more likely to trigger the target error. For a given target program location, the static analyzer estimates sufficient conditions for the target error. During the synthesis, UnitCon checks if the partial test case can potentially satisfy the error conditions. If so, UnitCon prioritizes the partial test case.

## 4. Ground Check
It checks whether UnitCon has generated an executable test case. If it fails to generate one, the synthesis process is repeated. If an executable test case is generated, it is executed using the Tester to check whether the targeted exception is triggered. If the targeted exception is successfully reproduced, the test case is returned; otherwise, it is discarded.