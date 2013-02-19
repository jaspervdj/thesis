\documentclass{article}

%include polycode.fmt

% Used to hide Haskell code from LaTeX
\long\def\ignore#1{}

\title{Automatic detection of recursion patterns}

\begin{document}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\maketitle

\ignore{
\begin{code}
import Data.Char (toUpper)
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Abstract}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}

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
\section{Motivation}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Implementation}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Evaluation}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related work}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}

\end{document}
