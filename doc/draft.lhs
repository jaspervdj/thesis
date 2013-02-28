\documentclass{article}

% TODO: IEEE article format

%include polycode.fmt

\usepackage{amsmath}
\usepackage[numbers]{natbib}  % For URLs in bibliography

% Used to hide Haskell code from LaTeX
\long\def\ignore#1{}

\title{Automatic detection of recursion patterns}

\begin{document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\maketitle

\tableofcontents

\ignore{
\begin{code}
import Control.Arrow ((***))
import Data.Char     (toUpper)
import Prelude       hiding (head, foldr, map, sum)
\end{code}
}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Abstract}

Rewriting explicitly recursive functions in terms of higher-order functions such
as |fold| and |map| brings many advantages such as conciseness, improved
readability, and it facilitates some optimizations. However, it is not always
straightforward for a programmer to write functions in this style. We present an
approach to automatically detect these higher-order functions, so the programmer
can have his cake and eat it, too.

% TODO: Explicit results, evaluation

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}

% TODO: 2 paragraphs, 1 about own research/additions

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Motivation}

In early programming languages, developers manipulated the control flow of their
applications using the \texttt{goto} construct. This allowed \emph{arbitrary}
jumps through code, which brought with many disadvantages \cite{dijkstra1968}.
In particular, it could be very hard to understand code written in this style.

Later programming languages favored use of control stuctures such as
\texttt{for} and \texttt{while} over \texttt{goto}. This made it easier for
programmers and tools to analyze these structures, e.g. on pre- and
postconditions.

A similar argument can be made about \emph{arbitrary recursion} in functional
programming languages. Consider the functions:

\begin{code}
upper :: String -> String
upper []        = []
upper (x : xs)  = toUpper x : upper xs
\end{code}

\begin{code}
sum :: [Int] -> Int
sum []        = 0
sum (x : xs)  = x + sum xs
\end{code}

These functions can be rewritten using the \emph{higher-order} functions |map|
and |foldr|.

\begin{code}
map :: (a -> b) -> [a] -> [b]
map f []        = []
map f (x : xs)  = f x : map f xs
\end{code}

\begin{code}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z []        = z
foldr f z (x : xs)  = f x (foldr f z xs)
\end{code}

Which yields the more concise versions:

\begin{code}
upper' :: String -> String
upper' = map toUpper
\end{code}

\begin{code}
sum' :: [Int] -> Int
sum' = foldr (+) 0
\end{code}

The rewritten versions have a number of advantages.

\begin{itemize}
\item An experienced programmer will be able to read and understand the latter
versions much quicker: he or she immediately understands how the recursion works
by recognizing the higher-order function.

% TODO: Cite something on concise code can be read faster (some Scala study?)

\item The code becomes much more concise, which means there is less code to read
(and debug).

% TODO: Reword: When we prove properties for e.g. filter, we know that
% applications of filter also have these properties.

\item Some interesting and useful properties are immediately obvious: e.g.

\begin{spec}
length (filter f xs) <= length xs
\end{spec}

\item Last but not least, these properties allow for certain optimizations. Map
fusion is a well-known example \cite{meijer1991}:

\begin{spec}
map f . map g = map (f . g)
\end{spec}
\end{itemize}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Implementation}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Generalized foldr}

In this document, we focus on detecting |foldr| rather than |filter| or |map|,
because this pattern is more general than |map|. This becomes clear if we see
that |map| can be written in terms of |foldr|:

\begin{code}
map' :: (a -> b) -> [a] -> [b]
map' f = foldr (\x xs -> f x : xs) []
\end{code}

However, that is not the only way in which |foldr| is more general. A |foldr| is
a \emph{catamorphism} \cite{meijer1991} --- so it can be generalized to
arbitrary algebraic data types instead of just lists.

\begin{code}
data Tree a
    = Leaf a
    | Branch (Tree a) (Tree a)
\end{code}

\begin{code}
foldTree  ::  (a -> r)
          ->  (r -> r -> r)
          ->  Tree a
          ->  r
foldTree l _ (Leaf x)      = l x
foldTree l b (Branch x y)  =
    b (foldTree l b x) (foldTree l b y)
\end{code}

A general fold takes a number of functions as arguments, to be more precise,
exactly one function per possible constructor in the datatype. If we consider
the product of these functions as operators in an \emph{algebra}, applying a
catamorphism is simply interpreting the data structure in terms of an algebra.

This indicates the concept of a fold is a very general idea, which is an
important motivation: our work will apply to any algebraic datatype rather than
just lists.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{GHC Core}
\label{subsection:ghc-core}

There are two convenient representations of Haskell code which we can analyze.

A first option is to analyze the Haskell code directly. Numerous parsing
libraries exist to make this task easier \cite{haskell-src-exts}.

During compilation, the Haskell code is translated throughout a different number
of passes. One particulary interesting representation is GHC Core
\cite{tolmach2009}.

Analyzing GHC Core for folds gives us many advantages:

\begin{itemize}
\item GHC Core is much less complicated, because all syntactic features have
been stripped away.

\item The GHC Core goes through multiple passes. This is very useful since we
can rely on other passes to help our analysis. For example, it might be
impossible to recognize certain folds before a certain function is inlined.

\item We have access to type information, which we can use in the analysis.
\end{itemize}

However, we must note that there is a major drawback to analyzing GHC Core
instead of Haskell code: it becomes much harder (and outside the scope of this
project) to use the results for refactoring.

In GHC 7.2.1, a new mechanism to manipulate and inspect GHC Core was introduced
\cite{ghc-plugins}. We decided to use this system since it is much more
accessible than using the GHC API directly, especially when Cabal is used as
well.

This plugins mechanism allows us to manipulate expressions directly. We show a
simplified expresssion type here:

\ignore{
\begin{code}
data Id = Id
data Literal = Literal
data AltCon = AltCon
\end{code}
}

\begin{code}
data Expr
    = Var Id
    | Lit Literal
    | App Expr Expr
    | Lam Id Expr
    | Let Bind Expr
    | Case Expr Id [Alt]

data Bind
    = NonRec Id Expr
    | Rec [(Id, Expr)]

type Alt = (AltCon, [Id], Expr)
\end{code}

|Id| is the type used for different kinds of identifiers. The |Id|s used in this
phase of compilation are guaranteed to be unique, which means we don't have to
take scoping into account for many transformations. |Lit| is any kind of
literal. |App| and |Lam| are well-known from the $\lambda$-calculus. |Let| is
used to introduce new recursive or non-recursive binds, and |Case| is used for
pattern matching---the only kind of branching possible in GHC Core.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Identifying folds}
\label{subsection:identifying-folds}

% TODO: Talk about case expressions instead of Case constructs

% TODO: Try to describe our algorithm with a pattern/BNF + predicates

The trick in $fold$ is that we create an anonymous function which will allow us
to replace a specific argument with a subterm later.

\begin{spec}
<fold f>
    ::= <fold' f f>
\end{spec}

\begin{spec}
<fold' f f>
    ::= Lam x <foldOver (\y -> App f y) x>
      | Lam x <fold' (App f x) f>
\end{spec}

\begin{spec}
<foldOver f x>
    ::= Lam y <foldOver f x>
      | Case x of <alts f x>
\end{spec}

\begin{spec}
<alts f x>
    ::= <alt f x>
      | <alts f x>; <alt f x>
\end{spec}

\begin{spec}
<alt f x>
    ::= Constructor <subterms> <body>
\end{spec}

Since a fold applies an algebra to a datatype, we must have an operator from
this algebra for each constructor. We can retrieve this operator be writing it
as anonymous function based on |<body>|.

Our function $rewrite$ works on these $<alt>$ constructs by turning the body
into an anonymous function, step by step, by adding an argument for each
subterm.

If the subterm is recursive we expect a recursive call to $f$, otherwise we
treat the subterm as-is.

%format t1 = "t_1"
%format subst (term) (v) (e) = "\mathopen{}" term "[^{" v "}_{" e "}\mathclose{}"

\begin{spec}
rewrite f []        body  = body
rewrite f (t1 : ts) body
    | isRecursive t1      = Lam x (subst ((rewrite f ts body)) ((f t1)) x)
    | otherwise           = Lam x (subst ((rewrite f ts body)) t1 x)
\end{spec}

With the first argument to $Lam$, $x$, a fresh variable. Let's look at an
example.

\begin{spec}
sum :: [Int] -> Int
sum = \ad -> case ad of
    []        -> 0
    (x : xs)  -> x + sum xs
\end{spec}

If we rewrite the $:$ constructor in the $sum$ function, we get:

%format sub (x) = "\mathopen{}t_{" x "}\mathclose{}"
%format beta = "\beta"

\begin{spec}
rewrite (\t -> sum t) [sub x, sub xs] (sub x + sum (sub xs))
    = <definition rewrite>
        \x -> rewrite (\t -> sum t) [sub xs] (subst ((sub x + sum (sub xs))) (sub x) x)
    = <substitution>
        \x -> rewrite (\t -> sum t) [sub xs] (x + sum (sub xs))
    = <definition rewrite>
        \x y -> rewrite (\t -> sum t) [] (subst ((x + sum (sub xs))) ((\t -> sum t) (sub xs)) y)
    = <beta reduction>
        \x y -> rewrite (\t -> sum t) [] (subst ((x + sum (sub xs))) (sum (sub xs)) y)
    = <substitution>
        \x y -> rewrite (\t -> sum t) [] (x + y)
    = <definition rewrite>
        \x y -> x + y
\end{spec}

While this is a simple example, this also works in the more general case.

% TODO: Check that stuff is in scope.

% TODO: Try to explain the theorem: f is a fold <-> the args are well-scoped.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Degenerate folds}
\label{subsection:degenerate-folds}

The algorithm described in \ref{subsection:identifying-folds} also classifies
\emph{degenerate folds} as being folds. |head| is an example of such a
degenerate fold:

\begin{code}
head :: [a] -> a
head (x : _)  = x
head []       = error "empty list"
\end{code}

Can be written as a fold:

\begin{code}
head' :: [a] -> a
head' = foldr const (error "empty list")
\end{code}

Fortunately we can easily detect these degenerate folds: iff no recursive
applications are made in any branch, we have a degenerate fold.

These degenerate folds are of no interest to us, since our applications focus on
optimizations regarding loop fusion. In degenerate folds, no such loop is
present, and hence the optimization is futile.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Application: fold-fold fusion}

As we discussed in \ref{subsection:ghc-core}, the fact that we are working on
the level of GHC Core makes it hard to use our rewrite results for refactoring.
However, we can look at some interesting optimizations.

\emph{Fold-fold fusion} is a technique which fuses two folds over the same data
structure into a single fold. This allows us to loop over the structure only
once instead of twice.

\begin{code}
mean :: [Int] -> Double
mean xs = fromIntegral (sum xs) / fromIntegral (length xs)
\end{code}

If we know from previous analysis results that |sum| is a fold with arguments
|((+), 0)| and |len| is a fold with arguments |(const (+ 1), 0)|, we can apply
fold-fold fusion here:

% TODO: Describe the more generic pattern. Include definition of (***).

\begin{code}
mean' :: [Int] -> Double
mean' xs =
    fromIntegral sum' / fromIntegral len'
  where
    (sum', len') = foldr (\x -> (+ x) *** (+ 1)) (0, 0) xs
\end{code}

We can repeatedly apply this optimization to fuse an arbitrary amount of $n$
folds into a single fold with an $n$-tuple.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{When can we apply fold fusion?}

% TODO: Can we describe this using the same pattern syntax?

% TODO: We can actually always apply this because of laziness. However, it's not
% always an optimization. We must be more precise in our description.

% TODO: Don't talk about Let, Lam constructs, talk about expressions.

We can apply fold fusion when we find two folds with different algebras over the
same structure in the same \emph{branch}. Concretely, this means our detection
algorithm works as follows:

We first find an application of a function we previously idenfitied as fold. We
store a reference to the data structure $x$ which is folded over.

Then, we search the expression tree for other expressions in which we apply a
function to $x$. Our search scope is limited: we can descend into |Let|, |App|
and |Lam| constructs to search their subexpressions, but we cannot descent into
the branches of a |Case| construct.

If two folds appear in different branches of a |Case| construct, we will often
not have an actual optimization. Let's look at a simple counterexample:

\begin{code}
value :: [Int] -> Int
value xs
    | length xs < 3  = 0
    | otherwise      = sum xs
\end{code}

In this case, fold-fold fusion is definitely not an optimization if we choose
the |length xs < 3| branch in most cases: in fact, we even save work by not
creating a thunk for the |sum xs| result.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Evaluation}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Identifying folds}

A first aspect we can evaluate is how well our detection of folds works.
Unfortunately, manually identifying folds in projects takes too much time. This
explains why it is especially hard to detect false negatives.

% TODO: Don't say that hlint does a poor job, just say that our tool is better.
% Try to state that hlint finds a strict subset.

Additionally, very little other related work is done. The \emph{hlint} tool is
able to recognize a few folds, but its results appear rather poor compared
compared to our tool (in this particular area).

In Table \ref{tabular:project-results}, we can see the results of running our
tool on some well-known Haskell projects. We classify folds into three
categories:

\begin{itemize}
\item Degenerate folds, as described in \ref{subsection:degenerate-folds};
\item List folds, folds over data structures of type |[a]|;
\item Data folds, folds over any other data structure.
\end{itemize}

\begin{table}
\begin{center}
\begin{tabular}{l||rrr||r}
                    & Degenerate folds & List & Data& hlint \\
\hline
\textbf{hlint}      &  248             & 17   & 25  & 0     \\
\textbf{parsec}     &  150             &  6   &  0  & 0     \\
\textbf{containers} &  311             &  7   & 75  & 0     \\
\textbf{pandoc}     & 1012             & 35   &  1  & 0     \\
\textbf{cabal}      & 1701             & 43   & 30  & 1     \\
\end{tabular}
\label{tabular:project-results}
\caption{Results of identifying folds in some well-known projects}
\end{center}
\end{table}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Optimization results}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related work}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}

% References
\bibliographystyle{plainnat}
\bibliography{references}

\end{document}
