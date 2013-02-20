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
import Data.Char (toUpper)
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
upper1 :: String -> String
upper1 []        = []
upper1 (x : xs)  = toUpper x : upper1 xs
\end{code}

\begin{code}
evens1 :: [Int] -> [Int]
evens1 []         = []
evens1 (x : xs)
    | even x      = x : evens1 xs
    | otherwise   = evens1 xs
\end{code}

\begin{code}
sum1 :: [Int] -> Int
sum1 []        = 0
sum1 (x : xs)  = x + sum1 xs
\end{code}

These functions can all be rewritten using \emph{higher-order} functions. We
obtain these versions:

\begin{code}
upper2 :: String -> String
upper2 = map toUpper
\end{code}

\begin{code}
evens2 :: [Int] -> [Int]
evens2 = filter even
\end{code}

\begin{code}
sum2 :: [Int] -> Int
sum2 = foldr (+) 0
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

We want to analyze if $f$ is a fold. $f$ takes arguments $a_i ... a_n$.

A fold works by unconstructing a single argument, so we examine the function
body if we see an immediate top-level \texttt{Case} construct. If there is such
a constructor, and the \texttt{Case} statement destroys an argument $a_i$, we
can assume we are folding over this argument (given that $f$ is a fold --- which
we still need to check). Let this $a_i$ be $a_d$.

Let's look at an example: in \texttt{sum1}, the first and only argument is this
$a_d$.

\begin{spec}
sum1 :: [Int] -> Int
sum1 ad = case ad of
    []        -> 0
    (x : xs)  -> x + sum1 xs
\end{spec}

Then, we analyze the alternatives in the \texttt{Case} statement. For each
alternative, we have a constructor $c$, a number of subterms bound by the
constructor $t_j$, and a body $b$.

We make a distinction between recursive and non-recursive subterms. We can step
through the subterms and rewrite the body $b$ as we go along.

For a non-recursive subterm $t_j$,

\begin{equation}
b' = (\lambda x. b [^{t_j}_x) t_j
\end{equation}

For a recursive subterm $t_j$, we can write the recursive call $r$ by applying
$f$ to the arguments

\begin{equation*}
\begin{cases}
t_j & \text{if} ~ i = d \\
a_i & \text{otherwise}  \\
\end{cases}
~ \forall i \in [1 ... n]
\end{equation*}

And in this case, the body is rewritten as:

\begin{equation}
b' = (\lambda x. b[^r_x) r
\end{equation}

After this rewriting stage, we have a new body $b'$ for each alternative of the
\texttt{Case} construct. Each body is an anonymous function which takes subterms
and recursive applications as arguments. In our example, we have:

\begin{spec}
sum1 :: [Int] -> Int
sum1 ad = case ad of
    []        -> 0
    (x : xs)  -> (\t1 t2 -> t1 + t2) x (sum1 xs)
\end{spec}

We immediately see the bodies of these functions are exactly the arguments to
the fold!

\begin{spec}
sum1 :: [Int] -> Int
sum1 = foldr (\t1 t2 -> t1 + t2) 0
\end{spec}

% TODO: Check that stuff is in scope.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Application: fold-fold fusion}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Evaluation}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related work}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}

\end{document}
