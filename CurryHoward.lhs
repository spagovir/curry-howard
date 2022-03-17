\documentclass[12pt]{article}
%include polycode.fmt
\newcommand{\proves}{\vdash}
\usepackage{amsthm}
\usepackage{amsmath}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem*{remark}{Remark}

\title{The Curry-Howard Isomorphism for Propositional Logic}
\date{2022 February 28}
\author{Edgar Lin}
\begin{document}
\maketitle
\section{Introduction}
Intuitionistic logic attempts to formalize the the \textit{BHK-interpretation} (named for Brouwer, Heyting, and Kolmogorov) of logical connectives. 
In particular, the BHK-interpretation of the logical connective $\to$ holds that a proof of $\varphi_1\to\varphi_2$ is a program transforming any demonstration of $\varphi_1$ into one of $\varphi_2$. 
In order to demonstrate that a proof-system in intuitionistic logic properly formalizes the BHK-interpretation, then, we would like to show that any proof of $\varphi_1\to\varphi_2$ does in fact correspond to a program in some formalism of computation that takes some representation of a proof of $\varphi_1$ to a proof of $\varphi_2$.  

This correspondence is called the Curry-Howard correspondence. Here, we will explicate the Curry-Howard correspondence between the natural deduction proof-system for the implicational fragment of intuitionistic propositional logic, that is, the subset of intuitionistic propositional logic that only uses the logical connectives $\to$ and $\bot$, and the simply-typed lambda calculus, a formalism for representing computable functions. 

The Curry-Howard isomorphism goes as follows: first, we interpret sentences in propositional logic as types of expressions in the simply-typed lambda calculus, in particular, we interpret sentences of the form $\varphi\to\psi$ as types of functions from expressions of the type corresponding to $\varphi$ to expressions of the type corresponding to $\psi$. 
Then, a proof of a sentence is simply an expression in the simply-typed lambda calculus whose type is that sentence. The Curry-Howard isomorphism, then, statesthat provability in intuitionistic propositional logic is equivalent to type-inhabitation in the simply typed lambda-calculus by providing a one-to-one correspondence between every natural deduction proof of a sentence in intuitionistic propositional logic and every term in the simply-typed lambda calculus such that the type of the lambda-term is the sentence to be proved. Further, this correspondence is computable by a structure-preserving transformation between the abstract syntax-trees of the proof and the program.  

In the following sections, we will outline the implicational fragment of intuitionistic propositional logic (IPC($\to$)) along with the natural deduction proof system, before demonstrating the Curry-Howard isomorphism between the two systems and some of its uses and abuses. When it comes to demonstrating the computational properties of the correspondence, we will write our computations as Haskell programs instead of using formal systems of defining computations for the sake of readability. 
 
\section{The Natural Deduction Proof System for the IPC($\to$)}
The syntactic rules for the implicational fragment of intuitionistic propositional formulae are much the same as that for classical logic. 
We start with a countably infinite set of propositional variables/atomic propositions $PV$. In the implicational fragment we only have one logical connective, $\to$, signifying implication. Then, our set of formulae/sentences $\Phi$ is 
the smallest set of finite strings of characters in containing all of the below: 
\begin{itemize}
\item Every $A\in PV$, 
\item $(A\to B)$ for every $A,B\in \Phi$. 
\end{itemize} 

We note that in particular that we can't explicitly express $\bot$ in the implicational fragment. Thus, the implicational fragment is called a \textit{positive} subset of the full intuitionistic logic. We will later show that this omission doesn't affect the set of (implicational) sentences we can prove. 

We will assume the unique reading lemma. Then, we can equivalently define logical formulae as strings corresponding to the following abstract syntax tree (in Haskell):  
\begin{code}
module CurryHoward where
import qualified Data.Set as Set
import qualified Data.List as List

type PV = String 
data Formula = Atomic PV 
               | Implies Formula Formula 
               deriving (Show, Eq, Ord) 
\end{code}

The conversion back to strings goes as follows:
\begin{code}
formula :: Formula -> String 
formula (Atomic v) = v
formula (Implies p q) = "(" ++ formula p ++ "\\to " ++ formula q ++ ")" 
\end{code}

A \textit{theory} is a subset $\Gamma\subset\Phi$. We call a finite theory $\Gamma$ a \textit{context}. 
For a formula $\varphi$ we wrote $\Gamma,\phi$ for $\Gamma\cup\{\varphi\}$. 
\begin{code}
type Theory = Set.Set Formula
\end{code}
For a context $\Gamma$ and a formula $\varphi$ we write $\Gamma\vdash\varphi$ to denote the fact that $\Gamma$ proves $\varphi$.  
We call any $\varphi$ such that $\vdash\varphi$ a theorem of IPC($\to$). 
A proof of $\Gamma\vdash\varphi$ is a (finite) tree whose nodes are labeled with context-formula pairs, which we will denote $\Delta\vdash\psi$, and that obey the following rules:
\begin{itemize}
\item The root node is labeled by $\Gamma\vdash\varphi$, that is, the conclusion of the proof.  
\item The leaf nodes are labeled $\Delta,\psi\vdash\psi$. These correspond to using an axiom in a proof. 
\item Non-leaf nodes have one or more children. The labels of parent nodes are inferred from those of their children by one of the following rules: 
\begin{itemize}
\item Introduction of $\to$ ($\to$ I): From $\Delta,\psi\vdash \pi$, infer $\Delta\vdash\psi\to\pi$.    
\item Elimination of $\to$ ($\to$ E): From $\Delta\vdash \psi\to\pi$ and $\Delta\vdash \psi$, infer $\Delta\vdash \pi$. 
\end{itemize}
\end{itemize}
We can write a natural deduction tree and proof-checking rules in Haskell as follows:
\begin{code}
data Proof = Axiom (Theory, Formula) 
             | Introduction (Theory, Formula) Proof 
             | Elimination (Theory, Formula) Proof Proof 
             deriving (Show, Eq)
label :: Proof -> (Theory, Formula) 
label (Axiom a) = a
label (Introduction a _) = a
label (Elimination a _ _) = a  
valid :: Proof -> Bool
valid (Axiom (g, p)) = Set.member p g
valid (Introduction (g, Implies p q) c) = 
  (fst $ label c) == Set.insert p g && (snd $ label c) == q
valid (Introduction _ _) = False 
valid (Elimination (g, p) major minor) = 
  (fst $ label major) == g 
  && (fst $ label minor) == g 
  && (snd $ label major) == Implies (snd $ label minor) p 
\end{code}
We note that we usually use the following notation to write nodes of natural deduction trees: $$\frac{Children}{Label},$$
ie, proof trees are displayed according to the program below: 
\begin{code}
asTex :: Proof -> String
asTex (Axiom a) = showLabel a
asTex (Introduction a c) = 
  "\\dfrac{" 
  ++ asTex c 
  ++ "}{" 
  ++ showLabel a 
  ++ "}"
asTex (Elimination a c1 c2) = 
  "\\dfrac{" 
  ++ asTex c1 
  ++ "\\," 
  ++ asTex c2 
  ++ "}{" 
  ++ showLabel a 
  ++ "}" 
showLabel (g,p) = "\\{" ++ (concat $ List.intersperse "," $ map formula $ Set.toList g) ++ "\\}\\vdash " ++ formula p
\end{code}

\subsection{Natural Deduction \& BHK}
We can interpret the rules of natural deduction in BHK as follows. First, we take $\{\varphi_1,\varphi_2,\dots,\varphi_n\}\vdash \psi$ as 
``Given (black-box) demonstrations for each $\varphi_i$, there is some construction built out of the $\varphi_i$ that is a demonstration of $\psi$.''
Then, we can interpret the $\to$I rule, $\frac{\Gamma,\phi\vdash\psi}{\Gamma\vdash\phi\to\psi}$ as follows: 
``We have that given demonstrations for the contents of $\Gamma$ and for $\phi$ we can build out of those demonstrations a demonstration of $\psi$. 
Then, using the demonstrations for the contents of $\Gamma$, we can write that demonstration of $\psi$ with the demonstrations for $\phi$ erased 
and then write a program that takes as input a new demonstration of $\phi$ and inserts it into the blanks where the old demonstrations for $\phi$ were.  
This program takes as input a demonstration of $\phi$ and produces a demonstration of $\psi$, so it is a proof of $\phi\to\psi$.''
Finally, the $\to$E rule can be interpreted as applying the program that is the proof of the major premise to the proof of the minor premise 
to get a proof of the conclusion. 

\subsection{Natural Deduction \& Hilbert-Style Proofs}
Recall the Hilbert-style proof system for classical logic where we had only one inference rule, modus ponens, and instead had three axiom schemes
(we assume that $\to$ associates to the right for brevity):
\begin{itemize}
\item[$P_1$:] $\phi\to\psi\to\phi$. 
\item[$P_2$:] $(\phi\to\psi\to\chi) \to (\phi\to\psi)\to\phi\to\chi$.
\item[$P_3$:] $((\phi\to\bot)\to\bot)\to\phi$. 
\end{itemize}
The $\to$E rule clearly corresponds to modus ponens. 

What does $\to$I correspond to? We note that $P_1$ and $P_2$ in the Hilbert proof system are sufficient to prove the deduction theorem: 
\begin{theorem}[Deduction Theorem]
In the Hilbert proof system with only axioms $P_1$ and $P_2$, if $\Gamma,\phi\vdash\psi$, then, $\Gamma\vdash\phi\to\psi$.
\end{theorem}
We will delay the proof until we have introduced a slight variation on proof trees in order to prove a slightly stronger version of the theorem.
 
Further, we can show that every member of the axiom schemes $P_1$ and $P_2$ are theorems of IPC($\to$) in natural deduction: 
\begin{theorem}
For any triplet of propositions $(\phi, \psi,\chi)$, denote their corresponding axioms in the axiom schemes $P_1$ and $P_2$
as $P_{1,\phi,\psi}$ and $P_{2,\phi,\psi,\chi}$ respectively.  
Then, for all $\phi,\psi,\chi\in\Phi$, we have that in IPC($\to$), $\vdash P_{1,(\phi,\psi)}$ and $\vdash P_{2,(\phi,\psi,\chi)}$. 
\begin{proof}
For any $\phi,\psi$, the following is a natural deduction proof of $P_{1,\phi,\psi}$:
$$\frac{\dfrac{\phi ,\psi \vdash \phi }{\phi \vdash (\psi \to \phi )}}{\vdash (\phi \to (\psi \to \phi ))}.$$
We delay the proof of $P_2$ until after we have the Curry-Howard Isomorphism. 
\end{proof}
\end{theorem} 

\subsection{Intuitionistic Algebraic Semantics}
We would like to dwell a bit on the semantics of intuitionistic logic before moving on to the simply typed lambda-calculus. 
In specific, we would like to show that the set of statements provable by natural deduction in the implicational fragment 
is equal to the set of statements that are \textit{semantically} necessarily true according to the algebraic semantics
of the full system of intuitionistic logic. 

Further, we want to use the semantics of logical deduction to illustrate some important differences between intuitionistic logic
and classical logic. 
We noted in the previous section that natural deduction for the implicational fragment of intuitionistic logic corresponds to 
the Hilbert proof system in classical logic without the axiom $((\phi\to\bot)\to\bot)\to\phi$. 
This axiom can be interpreted as formalizing the idea of a proof (of a positive statement) by contradiction: 
that is, if $\neg\phi$ proves a contradiction, then $\phi$ must be true. 
The fact that this axiom is not given in intuitionistic logic can be seen as a consequence of the \textit{constructive} nature
of intuitionistic logic: it's not clear how a construction of a contradiction out of $\phi\to\bot$ can directly be used to make a
construction of $\phi$ itself.  
We would like to be able to actually prove that intuitionistic logic can't actually prove that in general $((\phi\to\bot)\to\bot)\to\phi$. 
We can do this semantically by appeal to a topological interpretation of the algebraic semantics of intuitionistic logic. 

\subsubsection{The Lindenbaum-Tarski Algebra of IPC($\to$)}
Let's try to construct the algebraic semantics of the full intuitionistic propositional calculus from the semantics of its implicational fragment.

Consider a theory $\Gamma$, and the following lemma about natural deduction:
\begin{lemma}
Let $\Gamma$ be a theory in $IPC(\to)$. Then the following are true:
\begin{itemize}
\item[1.] $\Gamma\vdash \varphi\to\varphi$
\item[2.] If $\Gamma\vdash \varphi\to\psi$ and $\Gamma\vdash \psi\to\chi$, then $\Gamma\vdash\varphi\to\chi$.
\item[3.] If $\Gamma\vdash \varphi\leftrightarrow\varphi'$, $\Gamma\vdash\psi\leftrightarrow\psi'$, and $\Gamma\vdash\varphi\to\psi$, 
then, $\Gamma\vdash\varphi'\to\psi'$. 
\begin{proof}
\begin{itemize}
\item[1.] $$\dfrac{\Gamma,\varphi\vdash\varphi}{\Gamma\vdash\varphi\to\varphi}.$$
\item[2.] Let $\frac{\Pi[\cup\Delta]}{\Gamma\cup\Delta\vdash \varphi\to\psi}$ be a proof of $\Gamma\vdash\varphi\to\psi$
with every instance of $\Gamma$ replaced with $\Gamma\cup\Delta$, 
and $\frac{\Sigma[\Delta]}{\Gamma\cup\Delta\vdash \psi\to\chi}$ be a proof of $\Gamma\vdash \psi\to\chi$ 
with the same substitutions.  
Then, 
$$
\dfrac{
\dfrac{
  \dfrac{\Gamma,\varphi\vdash\varphi\text{ } \Gamma,\varphi\vdash \varphi\to\psi}{\Gamma,\varphi\vdash\psi}\text{ }
  \Gamma,\varphi\vdash\psi\to\chi
  }
  {
  \Gamma,\varphi\vdash\chi
  }
}
{
  \Gamma\vdash\varphi\to\chi
}
$$
\item[3.] Follows from two applications of (2.).
\end{itemize}
\end{proof}
\end{itemize}
\end{lemma} 
Items (1.) and (2.) from the above lemma means that if we define $\phi\leq_\Gamma \psi$ as $\Gamma\vdash \phi\to\psi$ 
for any two formulae $\phi,\psi\in\Phi$ 
(or equivalently, $\Gamma,\phi\vdash\psi$), 
$\leq_\Gamma$ forms a preorder on the set of formulas $\Phi$. 
Then, defining the equivalence relation $\phi\sim_\Gamma\psi\iff\Gamma\vdash\phi\leftrightarrow\psi$,
we get that $\Phi/\sim_\Gamma$ is a partially ordered set under $\leq_\Gamma$ 
where the largest element, which we can denote as $1$, is the set of $\phi$ such that $\Gamma\vdash\phi$---
we note (1.) implies that this class is non-empty.  
We call $\Phi/\sim_\Gamma$ the \textit{Lindenbaum-Tarski algebra} for $\Gamma$. 

Further, item (3.) means that the connective $\to$
induces a binary operator $\to_\Gamma$ on $\Gamma\vdash\phi$ such that $[\psi]_\sim\to_\Gamma[\phi]_\sim=[\psi\to\phi]_\sim$.
The operator $\to_\Gamma$ obeys the axiom that $\phi\to_\Gamma\psi = 1$ if and only if $\phi \leq_\Gamma \psi$. 

We can interpret elements of $\Phi/\sim_\Gamma$ as classes of formulae that are semantically-equivalent
in the sense that the set of formulae whose demonstrations can be constructed from those 
of each element in the class are the same. 

\subsubsection{Heyting Algebras}
In the previous section we defined a way to assign semantic values to formulae
in a theory $\Gamma$ such formulae with the same semantic value could be considered
logically equivalent under $\Gamma$.
We noted that the semantic values have the structure of a partially ordered set
with a greatest element and has a single binary operator that interprets the
implicational fragment's single logical connectives. 

We would like to define an algebraic structure that can be used to assign values
to statements in the full intuitive propositional calculus with its full complement
of logical connectives: $\wedge,\vee,$ and $\bot$. 
We will call this algebraic structure a \textit{Heyting Algebra} $\mathcal{H}=(H,\vee,\wedge,\to,0,1)$. 

We would like $\vee$ and $\wedge$ to still obey the distributive lattice axioms. 
We will interpret $\bot$ as absurdity, and stipulate that in intuitive logic $\bot$ follows
the principle of explosion: for any $\phi$ and any $\Gamma,$ $\Gamma\vdash\bot\to\phi$. 
Thus we will interpret $\bot$ as always having the value of the least element, $0$, of the Heyting algebra.
 




\subsubsection{Soundness and Completeness}
\subsubsection{Topological Intepretation of Heyting Algebras}
\section{Simply-Typed Lambda Calculus}
We remember that in the BHK-interpretation a proof $\varphi\to\psi$ should correspond 
to a program that takes a proof of $\varphi$ and returns a proof of $\psi$. 
If we are to identify proofs with programs, then a proof of $\varphi\to\psi$ would then
be identified with a program that takes a program and returns another program. 
It would then be desirable to have a formal model of computation where the basic domain of programs
are other programs. 
This model of computation will be called the \textit{simply-typed lambda calculus}. 

Here, we will present the Church-system of simply-typed lambda calculus. 
We will note that there is also a Curry-system of simply-typed lambda calculus,
that is mostly equivalent. 

In the simply-typed lambda calculus, we have two sorts of objects: types and terms. 
Both types and terms will be using \textit{syntactic} rules; 
meanwhile, terms will be assigned at most one type by the \textit{typability} relation;
we can think of the subset of terms that can be assigned types as the set of terms that are
\textit{semantically} well-defined.  
A type in the simply-typed lambda calculus will be a string following the same syntactic rules as propositions in IPC($\to$). 
Thus we can immediately identify the set of simple types with $\Phi$.\footnote{
The types in the simply-typed lambda calculus are called ``simple'' as they lack (a) parameters or (b) recursion. 
For example, the following |List| type definition in Haskell would not be a simple type: 
\begin{spec}
List a = Cons a (List a) | Empty
\end{spec}
} 
In the context of the simply-typed lambda calculus, members of $PV$ are called \textit{type variables}. 

Syntactically, programs in the lambda-calculus are first written in terms of the rules for forming \textit{pre-terms}. 
We begin with a countably infinite alphabet of variables $V$. 
Then, the set $\Lambda_\Phi^-$ of pre-terms is the smallest set of strings containing $V$ and closed under the following rules:
\begin{itemize}
\item If $x\in V$, $\phi\in\Phi$, and $M\in \Lambda_\Phi^-$, then, $(\lambda x .\phi \; M)\in \Lambda_\Phi^-$.
This rule is called \textit{abstraction} and can be roughly interpreted as defining a function $f\colon \phi\to \mathord{?}$ 
that can be written as $f(x) = M$. 
\item If $M,N\in \Lambda_\Phi^-$, then, $(M\; N)\in\Lambda_\Phi^-$. 
This rule is called \textit{application}; if $M$ evaluates to some function $f$ this should represent $f(N)$.  
\end{itemize}

That is, $\Lambda_\Phi^-$ corresponds to the set of strings representing the following Haskell data structure:
\begin{code}
type V = String
data Term = Variable V 
          | Abstraction V Formula Term 
          | Application Term Term
\end{code}

For a pre-term $M\in \Lambda_\Phi^-$ in the lambda calculus, we call the set of variables $x$ appearing in $M$ 
outside of an abstraction term $(\lambda x.\phi \; M)$ the set of \textit{free variables} $FV(M)$. 
More formally, the set of free variables is defined inductively such that 
\begin{itemize}
\item $FV(x) = \{x\}$,
\item $FV(\lambda x. \phi \; M) = FV(M)\setminus\{x\}$, 
\item $FV(M\; N)= FV(M)\cup FV(N)$. 
\end{itemize} 

The basic model of lambda calculus is computation by executing symbolic substitution rules. 
For a pre-term $M$ we write $M[x:=N]$ to denote the substitution of $N$ for $x$ in $M$. 
In doing so, we replace every \textit{free} instance of $x$ in $M$ by $N$, 
while preserving the set of free variables of $N$. 
Thus substitution is defined inductively as follows: 
\begin{itemize}
\item $x[x:=N] = N$
\item $y[x:=N] = y$ for $y\neq x$. 
\item $(P\; Q)[x:=N] = (P[x:=N]\; Q[x:=N])$.
\item $(\lambda x.\phi\; P)[x:=N] = (\lambda x.\phi\; P)$: instances of $x$ in $P$ are not free, so we don't replace them. 
\item $(\lambda y.\phi\; P)[x:=N] = (\lambda y.\phi\; P[x:=N])$ when $y\neq x$ and $y\notin FV(N)$: 
in this case the instances of $x$ in $P$ are still free, so should be replaced. 
We note that we run into a bit of difficulty when $y$ is a free variable of $N$: 
we want substitution to preserve the semantic meaning of $N$, 
wherein $y$ is a free variable referring to something in the outside context. 

Substituting $N$ directly into $P$ would cause $y$ to become bound by $\lambda y$, 
changing the meaning of $N$ as the instances of $y$ in $N$ would now refer to 
the argument variable $y$ of the lambda term. 

The solution is to stipulate that the names of argument variables used in a function definition
shouldn't matter: ie, $f(x) = g(x)$ should define the same function as $f(y) = g(y)$. 
Thus, we will rename the $y$ variable in the original abstraction term to something
that doesn't conflict with $N$ before substituting $N$ in. This leads us to our last rule: 
\item $(\lambda y.\phi\; P)[x:=N] = (\lambda z. \phi\; P[y:=z][x:=N])$ for some choice of $z\notin FV(P)\cup FV(N)$ when $y\neq x$ and $y\in FV(n)$. 
\end{itemize}
\subsection{Church-Rosser Theorem} 
\subsection{Weak-Normalization}
\subsection{Computational Power of Typed and Untyped Lambda Calculus}
\section{The Curry-Howard Isomorphism}
\subsection{Natural Deduction Proofs with Labeled Assumptions}
\subsection{Proof of the Isomorphism}
\subsection{Application: Consistency}
\subsection{Application: Untypability of the Y combinator}
\subsection{Application: Combinatory Logic \& Hilbert System}





\end{document}

