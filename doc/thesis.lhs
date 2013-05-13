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

\newcommand{\TODO}[1]{\textbf{(TODO: #1)}}


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

Deze programmeertalen bieden een hoog niveau van abstractie, en moedigen de
programmeurs aan om gebruik te maken van \emph{higher-order} functies (bv.
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

Er zijn dus weinig redenen om in deze talen expliciete recursie te gebruiken
wanneer een higher-order functie beschikbaar is. Toch blijkt dat veel
programmeurs nog gebruik maken van expliciete recursie.

Enkele redenen hiervoor zijn bijvoorbeeld dat de programmeur niet bekend is met
de higher-order functie, of dat er geen tijd is om de functie te refactoren. We
zien zelfs dat we voorbeelden terugvinden van expliciete recursie in code
geschreven door geavanceerde gebruikers van functionele programmeertalen
\TODO{cite: GHC HQ does it}.

De voordelen die hierboven beschreven staan vormen een motivatie om te
onderzoeken of het niet mogelijk is om deze functies, geschreven in expliciet
recursieve stijl, automatisch om te zetten in functies die gebruik maken van de
higher-order hulpfuncties. Op die manier kan de programmeur code schrijven in om
het even welke stijl, en toch genieten van de verschillende optimalisaties.

In dit document beschrijven we een aanpak om dit mogelijk te maken.

\TODO{Kort overzicht van de verschillende hoofdstukken}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Achtergrond}

We kozen voor de functionele programmeertaal Haskell \cite{jones2003} omwille
van verschillende redenen:

\begin{itemize}[topsep=0.00cm]

\item Een grote variatie higher-order functies is beschikbaar in het Prelude en
in de aanvullende libraries.

\item Haskell is een sterk getypeerde programmeertaal. Deze types geven ons meer
informatie die we kunnen gebruiken in de transformaties.

\item De de-facto standaard Haskell Compiler, GHC \cite{ghc}, laat via een
plugin-systeem toe om code te manipuleren op een relatief eenvoudige manier
\TODO{Cite het deel over GHC plugins/implementatie...}.

\end{itemize}

In dit hoofdstuk geven we een kort overzicht van Haskell, en de relevante
higher-order functies voor dit werk.

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
