%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\documentclass[12pt]{report}

\usepackage[dutch]{babel}
\usepackage[font=it]{caption}
\usepackage[left=1.90cm, right=1.90cm, top=1.90cm, bottom=3.67cm]{geometry}
\usepackage[numbers]{natbib}  % For URLs in bibliography
\usepackage[xetex]{graphicx}
\usepackage{fontspec,xunicode}
\usepackage{enumitem}
\usepackage{listings}
\usepackage{titlesec}
\usepackage{url}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include polycode.fmt

% Used to hide Haskell code from LaTeX
\long\def\ignore#1{}

\ignore{
\begin{code}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Rank2Types      #-}
import Data.Char     (toUpper)
import Prelude       hiding (head, foldr, map, sum, replicate)
\end{code}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Style
% \defaultfontfeatures{Mapping=tex-text,Scale=MatchLowercase}
\setmainfont{DejaVu Serif}
\setmonofont{Inconsolata}
\newfontfamily\futura{Futura Std}

\newcommand{\chapterstyle}{\futura\huge}
\titleformat{\chapter}
  {\chapterstyle}  % format
  {}               % label
  {0.00cm}         % sep
  {}               % before
  [\normalfont]    % after

\setlength{\parindent}{0.00cm}
\setlength{\parskip}{0.50cm}

\lstset{basicstyle=\ttfamily, keywordstyle=\ttfamily\bf}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{\futura\Huge Automatische detectie van recursiepatronen}
\author{Jasper Van der Jeugt}

\begin{document}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\maketitle
\tableofcontents


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Inleiding}

Laten we beginnen in het begin. Sinds er programmeertalen gebruikt worden, maakt
men gebruik van \emph{controlestructuren}. Deze laten toe de manier waarop het
programma wordt uitgevoerd te be\"invloeden. In assembleertaal zijn dit de
verschillende \emph{jump} instructies (\texttt{jmp}, \texttt{je}...).

Latere programmeertalen (bv. C), die op hoger niveau werken, voegden
controlestructuren van hoger niveau toe, zoals bijvoorbeeld \texttt{for}- en
\texttt{while}-lussen. Deze programmeertalen lieten echter meestal wel nog toe
om \emph{arbitraire} jumps te maken door middel van de \texttt{goto} instructie.
Dit wordt ge\"illustreerd in Figuur \ref{figure:for-vs-goto}.

\begin{figure}[h]
  \begin{minipage}[c]{0.5\textwidth}
    \begin{lstlisting}[language=C, gobble=4]
    int sum_squares_for(int n) {
      int i, sum = 0;

      for(i = 1; i <= n; i++) {
        sum += i * i;
      }

      return sum;
    }
    \end{lstlisting}
  \end{minipage}
  \begin{minipage}[c]{0.5\textwidth}
    \begin{lstlisting}[language=C, gobble=4]
    int sum_squares_goto(int n) {
      int i, sum = 0;

      i = 1;
      start: sum += i * i;
      i++;
      if(i <= n) goto start;

      return sum;
    }
    \end{lstlisting}
  \end{minipage}
  \caption{Twee semantisch equivalente programma's, \'e\'en met hoger-niveau
  controlestructuren en \'e\'en met \texttt{goto}'s}
  \label{figure:for-vs-goto}
\end{figure}

De versie die gebruikt maakt van \texttt{for} is eenvoudiger leesbaar voor
programmeurs die bekend zijn met dit concept. Ook is het mogelijk eigenschappen
uit te drukken over programmas die geschreven zijn in deze stijl, bijvoorbeeld
met Floyd-Hoare logica \cite{floyd1967}. Dit leidde zelfs tot de conclusie dat
het gebruik van \texttt{goto} volledig vermeden moet worden \cite{dijkstra1968}.

Een soortgelijke redenering is te maken over \emph{functionele
programmeertalen}. Deze talen maken geen gebruik van \texttt{goto} instructies,
maar implementeren controlestructuren door middel van \emph{recursie}.

Deze programmeertalen bieden een hoog niveau van abstractie bieden, en moedigen
de programmeurs aan om gebruik te maken van \emph{higher-order} functies (bv.
|map|, |filter|, |any|, \ldots). Op deze manier is geen expliciete recursie
nodig. Dit biedt verschillende voordelen:

\begin{itemize}[topsep=0.00cm]
\item Voor een programmeur die bekend is met de gebruikte higher-order functies
is mogelijk de code veel sneller te begrijpen: ze herkennen onmiddelijk het
patroon dat aangeboden wordt door de functie en dienen enkel de argumenten van
deze functie te bestuderen.

\item Door gebruik te maken van higher-order functies wordt de code beknopter.
Eerder is aangetoond dat het aantal fouten in code proportioneel is tot de
grootte van de codebase \cite{gaffney1984}. Hieruit kunnen we concluderen dat
het gebruik van higher-order functies het aantal fouten in programmas zou moeten
reduceren.

\item Het is mogelijk eigenschappen \'e\'enmaal te bewijzen over een
higher-order functie voor willekeurige argumenten. Dit spaart ons werk uit als
we willen redeneren over code, want de resultaten van deze bewijzen gelden dan
voor elke applicatie van deze higher-order functie.

\item Ook de compiler kan gebruik maken van deze eigenschappen, om verschillende
optimalisaties uit te voeren op de code.
\end{itemize}

\begin{itemize}
\item Hoog niveau
\item Dijksta etc
\item Overzicht geven
\end{itemize}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Achtergrond}

\begin{itemize}
\item Haskell, lambda
\item Higher order functions
\item Syntax
\item Wat zijn folds, toepassing
\item Wat zijn builds, toepassing
\end{itemize}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Detectie folds}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Detectie builds}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Implementatie \& evaluatie}

\begin{itemize}
\item Meer detail
\end{itemize}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Related work}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Conclusie}

\begin{itemize}
\item Samenvatting
\item Reflectie
\item Future work...
\end{itemize}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{abbrvnat}
\bibliography{references}

\end{document}
