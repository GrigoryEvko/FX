Logical Methods in Computer Science
Volume 17, Issue 3, 2021, pp. 11:1–11:67
https://lmcs.episciences.org/

Submitted Dec. 01, 2020
Published Jul. 28, 2021

# MULTIMODAL DEPENDENT TYPE THEORY

DANIEL GRATZER a, G.A. KAVVOS b, ANDREAS NUYTS c, AND LARS BIRKEDAL a

a Aarhus University
e-mail address: gratzer@cs.au.dk, birkedal@cs.au.dk

b University of Bristol
e-mail address: alex.kavvos@bristol.ac.uk

c Vrije Universiteit Brussel
e-mail address: andreas.nuyts@vub.be

ABSTRACT. We introduce MTT, a dependent type theory which supports multiple modalities. MTT is parametrized by a mode theory which specifies a collection of modes, modalities, and transformations between them. We show that different choices of mode theory allow us to use the same type theory to compute and reason in many modal situations, including guarded recursion, axiomatic cohesion, and parametric quantification. We reproduce examples from prior work in guarded recursion and axiomatic cohesion, thereby demonstrating that MTT constitutes a simple and usable syntax whose instantiations intuitively correspond to previous handcrafted modal type theories. In some cases, instantiating MTT to a particular situation unearths a previously unknown type theory that improves upon prior systems. Finally, we investigate the metatheory of MTT. We prove the consistency of MTT and establish canonicity through an extension of recent type-theoretic gluing techniques. These results hold irrespective of the choice of mode theory, and thus apply to a wide variety of modal situations.

# 1. INTRODUCTION

In order to increase the expressivity of Martin-Löf Type Theory (MLTT) we often wish to extend it with unary type operators that we call modalities or modal operators. Some modal operators arise as shorthands for internally definable structure [RSS20], while others are used as a device for internalising non-definable structure from particular models. In the latter case, we are sometimes even able to prove that a modality cannot be internally expressed—at least not without extensive changes to the judgmental structure of type theory: see e.g. the ‘no-go’ theorems by [Shu18, §4.1] and [LOPS18]. This paper is concerned with the development of a systematic approach to the judgmental formulation of type theories with multiple interacting modalities.

Key words and phrases: dependent type theory, modalities, modal type theory, categorical semantics, gluing.

LOGICAL METHODS
IN COMPUTER SCIENCE

DOI:10.46298/LMCS-17(3:11)2021

© D. Gratzer, G.A. Kavvos, A. Nuyts, and L. Birkedal
Creative Commons