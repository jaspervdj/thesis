\documentclass{article}

%include polycode.fmt

\usepackage{amsmath}

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
import Prelude       hiding (head, sum)
\end{code}
}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Abstract}

% TODO: 4-5 sentences: problem, motivation, solution

Rewriting explicitly recursive functions in terms of higher-order functions
brings many advantages such as conciseness, improved readability, and it even
allows for some optimizations. However, it is not always straightforward for a
programmer to write functions in this style. We present an approach to
automatically detect these higher-order functions, so the programmer can have
his cake and eat it, too.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}

% TODO: 2 paragraphs, 1 about own research/additions


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Motivation}

In early programming languages, developers manipulated the control flow of their
applications using the \texttt{goto} construct. This allowed \emph{arbitrary}
jumps through code, which brought with many disadvantages. In particular, it
could be very hard to understand code written in this style.

% TODO: Cite some stuff

Later programming languages favored use of control stuctures such as
\texttt{for} and \texttt{while} over \texttt{goto}. This made it easier for
programmers and tools to analyze these structures, e.g. on pre- and
postconditions.

A similar argument can be made about \texttt{arbitrary recursion} in functional
programming languages. Consider the functions:

\begin{code}
upper :: String -> String
upper []        = []
upper (x : xs)  = toUpper x : upper xs
\end{code}

\begin{code}
evens :: [Int] -> [Int]
evens []         = []
evens (x : xs)
    | even x      = x : evens xs
    | otherwise   = evens xs
\end{code}

\begin{code}
sum :: [Int] -> Int
sum []        = 0
sum (x : xs)  = x + sum xs
\end{code}

These functions can all be rewritten using \emph{higher-order} functions. We
obtain these versions:

\begin{code}
upper' :: String -> String
upper' = map toUpper
\end{code}

\begin{code}
evens' :: [Int] -> [Int]
evens' = filter even
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

\item The code becomes much more concise, which means there is less code to read
(and debug).

\item Some interesting and useful properties are immediately obvious: e.g.

\begin{spec}
length (filter f xs) <= length xs
\end{spec}

\item Last but not least, these properties allow for certain optimizations. Map
fusion is a well-known example:

\begin{spec}
map f . map g = map (f . g)
\end{spec}
\end{itemize}

% TODO: Cite


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Implementation}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{GHC Core}
\label{subsection:ghc-core}

There are two convenient representations of Haskell code which we can analyze.

\begin{itemize}
\item We can analyze the Haskell code directly. Numerous parsing libraries exist
to make this task easier. % TODO: Cite.

\item The Haskell code is translated through a different number of passes during
compilation. One particulary interesting representation is GHC Core.
\end{itemize}

Analyzing GHC Core for folds gives us many advantages:

\begin{itemize}
\item GHC Core is much less complicated, because all syntactic features have
been stripped away.

\item The GHC Core goes through multiple passes. This is very useful since we
can rely on other passes to help us. For example, it might be impossible to
recognize certain folds before a certain function is inlined.

\item We have access to type information, which we can use in the analysis.
\end{itemize}

However, we must that there is a major drawback to analyzing GHC Core instead of
Haskell code: it becomes much harder (and outside the scope of this project) to
use the results for refactoring.

In GHC 7.6, a new mechanism to manipulate and inspect GHC Core was introduced.
We decided to use this system since it is much more accessible than using the
GHC API directly, especially when Cabal is used as well. % TODO: Cite.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\subsection{Identifying folds}
\label{subsection:identifying-folds}

We want to analyze if $f$ is a fold. $f$ takes arguments $a_i ... a_n$.

A fold works by unconstructing a single argument, so we examine the function
body if we see an immediate top-level |Case| construct. If there is such a
constructor, and the |Case| statement destroys an argument $a_i$, we can assume
we are folding over this argument (given that $f$ is a fold --- which we still
need to check). Let this $a_i$ be $a_d$.

Let's look at an example: in |sum|, the first and only argument is this
$a_d$.

\begin{spec}
sum :: [Int] -> Int
sum ad = case ad of
    []        -> 0
    (x : xs)  -> x + sum xs
\end{spec}

Then, we analyze the alternatives in the |Case| statement. For each alternative,
we have a constructor $c$, a number of subterms bound by the constructor $t_j$,
and a body $b$.

We make a distinction between recursive and non-recursive subterms. We can step
through the subterms and rewrite the body $b$ as we go along.

For a non-recursive subterm $t_j$,

\begin{equation}
b' = (\lambda x. b [^{t_j}_x) t_j
\end{equation}

For a recursive subterm $t_j$, we can write the recursive application $r$ by
applying $f$ to the arguments

\begin{equation}
\begin{cases}
t_j & \text{if} ~ i = d \\
a_i & \text{otherwise}  \\
\end{cases}
~ \forall i \in [1 ... n]
\end{equation}

And in this case, the body is rewritten as:

\begin{equation}
b' = (\lambda x. b[^r_x) r
\end{equation}

After this rewriting stage, we have a new body $b'$ for each alternative of the
|Case| construct. Each body is an anonymous function which takes subterms and
recursive applications as arguments. In our example, we have:

\begin{spec}
sum :: [Int] -> Int
sum ad = case ad of
    []        -> 0
    (x : xs)  -> (\t1 t2 -> t1 + t2) x (sum xs)
\end{spec}

We immediately see the bodies of these functions are exactly the arguments to
the fold!

\begin{spec}
sum :: [Int] -> Int
sum = foldr (\t1 t2 -> t1 + t2) 0
\end{spec}

% TODO: Check that stuff is in scope.

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

We can apply fold fusion when we find two fold with different algebras over the
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

\end{document}
