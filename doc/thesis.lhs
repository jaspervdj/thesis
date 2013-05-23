%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\documentclass[12pt]{report}

\usepackage[dutch]{babel}
\usepackage[font={footnotesize, it}]{caption}
\usepackage[left=1.90cm, right=1.90cm, top=1.90cm, bottom=3.67cm]{geometry}
\usepackage[numbers]{natbib}  % For URLs in bibliography
\usepackage[xetex]{graphicx}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}
\usepackage{enumitem}
\usepackage{fontspec,xunicode}
\usepackage{listings}
\usepackage{titlesec}
\usepackage{url}

\newcommand{\TODO}[1]{\textbf{(TODO: #1)}}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%include polycode.fmt
%include forall.fmt

% Used to hide Haskell code from LaTeX
\long\def\ignore#1{}

\def\commentbegin{\quad\{\ }
\def\commentend{\}}

\ignore{
\begin{code}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE Rank2Types      #-}
import Data.Char  (toUpper)
import Data.List  (intersperse)
import GhcPlugins
import Prelude    hiding (filter, foldr, head, id, map, sum, product,
                          replicate)

elapsed :: a
elapsed = undefined
\end{code}
}

%format a'1 = "a^{\prime}_1"
%format a'2 = "a^{\prime}_2"
%format B1 = B"_1"
%format B2 = B"_2"
%format e1 = e"_1"
%format e'1 = "e^{\prime}_1"
%format e2 = e"_2"
%format e'2 = "e^{\prime}_2"
%format f1 = f"_1"
%format f2 = f"_2"
%format x1 = x"_1"
%format x2 = x"_2"
%format xs1 = xs"_1"
%format xs2 = xs"_2"

%format (many (x)) = "\overline{" x "}"
%format box = "\Box"
%format elapsed = "\ldots"
%format subst (term) (v) (e) = [v "\mapsto" e] term
%format triangle = "\triangle"


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Style
% \defaultfontfeatures{Mapping=tex-text,Scale=MatchLowercase}
\setmainfont[SmallCapsFont={Latin Modern Roman Caps}, Ligatures=TeX]{DejaVu Serif}
\setmonofont{Inconsolata}
\newfontfamily{\futura}[Scale=1.30]{Futura Std}

\newcommand{\chapterstyle}{\futura\huge}
\titleformat{\chapter}
  {\chapterstyle}  % format
  {\thechapter ~}  % label
  {0.00cm}         % sep
  {}               % before
  [\normalfont]    % after

\newcommand{\sectionstyle}{\futura\large}
\titleformat{\section}
  {\sectionstyle}
  {\thesection ~}
  {0.00cm}
  {}
  [\normalfont]

\newcommand{\subsectionstyle}{\futura}
\titleformat{\subsection}
  {\subsectionstyle}
  {\thesubsection ~}
  {0.00cm}
  {}
  [\normalfont]

\lstset{basicstyle=\ttfamily, keywordstyle=\ttfamily\bf}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Infer rules

\def\myruleform#1{
\setlength{\fboxrule}{0.5pt}\fbox{\normalsize $#1$}
}
\newcommand{\myirule}[2]{{\renewcommand{\arraystretch}{1.2}\begin{array}{c} #1
                      \\ \hline #2 \end{array}}}

\usepackage{mathpartir}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{\futura\Huge Automatische detectie van recursiepatronen}
\author{Jasper Van der Jeugt}

\begin{document}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\maketitle
\tableofcontents

\setlength{\parindent}{0.00cm}
\setlength{\parskip}{0.50cm}

% We have \checkmark, but we don't have \cross...
\def\tick{\checkmark}
\def\cross{$\times$}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Inleiding}

Laten we beginnen bij het begin. Reeds van bij de ontwikkeling van de eerste
computers, naar onze hedendaagse normen vrij rudimentaire machines, was het
noodzakelijk om in de gebruikte programmeertalen \emph{controlestructuren} te
voorzien. Deze instructies laten toe de manier waarop het programma wordt
uitgevoerd te be\"invloeden. In assembleertaal zijn dit de verschillende
\emph{sprong} instructies (\texttt{jmp}, \texttt{je}...). Typisch zal de
instructie voor de spronginstructie een testinstructie zijn. Enkel gebruik maken
van simpele tests en sprongen zonder duidelijke consistentie in de manier waarop
deze gebruikt worden kan echter leiden tot zogenaamde "spaghetti code". Daarmee
bedoelen we code die zowel moeilijk te lezen als te onderhouden is.

In latere programmeertalen (initieel talen zoals ALGOL, gevolgd door talen als
C), maakte het concept \emph{gestructureerd programmeren} een opmars.  Dit
betekent dat controlestructuren van een hoger abstractieniveau, zoals
bijvoorbeeld \texttt{for}- en \texttt{while}-lussen, werden ge\"introduceerd.
Deze programmeertalen laten echter meestal wel nog toe om \emph{expliciete}
sprongen te maken door middel van de \texttt{goto} instructie \footnote{Merk op
dat deze programmeertalen door een compiler worden omgezet naar machinetaal,
waarin wel nog sprongen voorkomen. Dit vormt echter geen probleem voor
leesbaarheid, sinds de meeste programmeurs deze machinetaal slechts zelden
zullen bekijken.}. Dit wordt ge\"illustreerd in Figuur \ref{figure:for-vs-goto}.

\begin{figure}[h]
  \begin{minipage}[t]{0.5\textwidth}
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
  \begin{minipage}[t]{0.5\textwidth}
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
  \caption{Twee semantisch equivalente programma's in de programmeertal C, links
  \'e\'en met hoger-niveau controlestructuren en rechts \'e\'en met
  \texttt{goto}'s.}
  \label{figure:for-vs-goto}
\end{figure}

De versie die gebruikt maakt van \texttt{for} is eenvoudiger leesbaar voor
programmeurs die bekend zijn met dit concept. Het is immers niet langer nodig om
de labels en \texttt{goto} instructies manueel te matchen en de relatie te
bestuderen: het gebruikte keyword kondigt onmiddelijk de gebruikt
controlestructuur aan (dit wordt meestal ook visueel ondersteund door gebruik te
maken van indentatie).

Bovendien is het mogelijk formele eigenschappen uit te drukken over programma's
die geschreven zijn in deze stijl, bijvoorbeeld met Floyd-Hoare logica
\cite{floyd1967}. Dit leidde zelfs tot de conclusie dat het gebruik van
\texttt{goto} volledig vermeden moet worden \cite{dijkstra1968}.

Een soortgelijke redenering is te maken over \emph{functionele
programmeertalen}. Deze talen maken geen gebruik van \texttt{goto} instructies,
maar implementeren controlestructuren door middel van \emph{recursie}.

Deze programmeertalen bieden een hoog abstractieniveau, en moedigen de
programmeurs aan om gebruik te maken van \emph{hogere-orde} functies (bv.
|map|, |filter|, |any|, \ldots). Op deze manier is geen expliciete recursie
nodig. Dit biedt verschillende voordelen:

\begin{enumerate}[topsep=0.00cm]
\item Voor een programmeur die bekend is met de gebruikte hogere-orde functies
is mogelijk de code veel sneller te begrijpen \cite{dubochet2009}: men herkent
onmiddelijk het patroon dat aangeboden wordt door de functie en dient enkel de
argumenten van deze functie te bestuderen.

\item Door gebruik te maken van hogere-orde functies wordt de code beknopter.
Eerder is aangetoond dat het aantal fouten in code proportioneel is tot de
grootte van de codebase \cite{gaffney1984}. Hieruit kunnen we concluderen dat
het gebruik van hogere-orde functies het aantal fouten in programma's zou moeten
reduceren.

\item Het is mogelijk eigenschappen \'e\'enmaal te bewijzen over een
hogere-orde functie voor willekeurige argumenten. Dit spaart ons werk uit als
we willen redeneren over code, want de bewijzen gelden dan voor elke applicatie
van deze hogere-orde functie.

\item Ook de compiler kan gebruik maken van deze eigenschappen, om verschillende
optimalisaties uit te voeren op de code.
\end{enumerate}

Deze redenen vormen een sterke motivatie om in deze talen geen expliciete
recursie te gebruiken als een hogere-orde functie beschikbaar is. Toch blijkt
dat veel programmeurs nog gebruik maken van expliciete recursie.

Enkele redenen hiervoor zijn bijvoorbeeld dat de programmeur niet bekend is met
de hogere-orde functie, of dat er geen tijd is om zijn zelfgeschreven functie te
herschrijven op basis van bestaande hogere-orde functies. We zien zelfs dat we
voorbeelden terugvinden van expliciete recursie in code geschreven door
gevorderde gebruikers van functionele programmeertalen \TODO{cite: GHC HQ does
it}.

De hierboven beschreven voordelen vormen de basismotivatie voor het onderzoek
dat we in deze thesis vericht hebben. We richten ons op functies die geschreven
zijn in een expliciete recursieve stijl en onderzoeken in welke gevallen het
mogelijk is deze automatisch om te zetten in functies die gebruik maken van de
hogere-orde hulpfuncties. Op die manier kan de programmeur code schrijven in om
het even welke stijl, en toch genieten van de verschillende optimalisaties.

We hanteren hiervoor de volgende concrete aanpak:

\TODO{Verwijs meer naar hoofdstukken hier}

\begin{enumerate}[topsep=0.00cm]

\item We tonen aan hoe functies die expliciete recursie gebruiken maar wel een
specifiek soort patroon (meer bepaald \emph{catamorfismes} \TODO{citatie?})
volgen kunnen gedetecteerd worden, en vertaald naar een versie die een
hogere-orde |fold| functie gebruikt in plaats van expliciete recursie.

\item Tevens leggen we ook uit hoe we functies die geschreven kunnen worden als
een toepassing van |build| kunnen detecteren en vertalen naar een versie die
effectief gebruikt maakt van |build|. Merk op dat |build| op zich geen
hogere-orde functie is, maar dat we zowel |fold| als |build| nodig hebben om
\emph{foldr/build-fusion} toe te passen, een bekende optimalisatie.

\item We implementeerden een GHC Compiler Plugin die deze detecties en
vertalingen automatisch kan uitvoeren tijdens de compilatie van een
Haskell-programma. Deze plugin werkt zowel voor de typische folds over lijsten
in Haskell (|[a]|), maar ook voor andere (direct) recursieve datatypes,
gedefini\"eerd door de gebruiker.

\item We onderzochten het aantal functies in enkele bekende Haskell programma's
die kunnen herschreven worden met behulp van de hogere orde functie |fold|. Deze
blijken in vele packages aanwezig te zijn. Ook bekijken we de resultaten van
enkele benchmarks na automatische |foldr/build-fusion|. Omdat
|foldr/build-fusion| de compiler toelaat om tussentijdse allocatie te vermijden,
zien we hier zeer grote versnellingen.

\end{enumerate}

We kozen Haskell als programmeertaal voor ons onderzoek. In het volgende
hoofdstuk zullen we kort ingaan op de eigenschappen van deze programmeertaal die
we gebruiken in deze thesis.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Achtergrond}

We kozen voor de pure functionele programmeertaal Haskell \cite{jones2003}
omwille van verschillende redenen:

\begin{itemize}[topsep=0.00cm]

\item Het Haskell Prelude \footnote{Het Prelude is de module die impliciet in
elk Haskell-programma wordt ge\"importeerd. De functies hieruit zijn dus
rechtstreeks te gebruiken zonder dat men een bibliotheek moet importeren.} en de
beschikbare bibliotheken bieden een waaier aan hogere-orde functies aan.

\item Haskell is een sterk getypeerde programmeertaal. Na het ini\"ele parsen en
typechecken van de code is deze type-informatie is beschikbaar in elke stap van
de compilatie. Deze types geven ons meer informatie die we kunnen gebruiken in
de transformaties. Bovendien maakt Haskell gebruik van type inference
\TODO{cite}, wat ervoor zorgt dat de programmeur meestal zelf geen types moet
opgeven.

\item De de-facto standaard Haskell Compiler, GHC \cite{ghc}, laat via een
pluginsysteem toe om code te manipuleren op een relatief eenvoudige manier
\TODO{Cite het deel over GHC plugins/implementatie...}.

\end{itemize}

In dit hoofdstuk geven we een zeer beknopt overzicht van Haskell, en lichten we
ook enkele relevante hogere-orde functies toe.

\section{Haskell: types en functies}
\label{section:haskell-types-and-functions}

Haskell is gebaseerd op de lambda-calculus. Dit is een formeel, doch eenvoudig
systeem, om aan logisch redeneren te doen. Het beschikt over een zeer beperkt
aantal basisoperaties. We beginnen onze Haskell-introductie dan ook bij de
lambda-calculus.

\begin{spec}
e ::= x        -- Een variabele
   |  e e      -- Functie-applicatie (links-associatief)
   |  \x -> e  -- Functie-abstractie (rechts-associatief)
\end{spec}

Dit is natuurlijk een zeer beperkte syntax en Haskell breidt deze sterk uit.
Beschouw bijvoorbeeld de volgende Haskell-functie (links) en het lambda-calculus
equivalent (rechts):

\begin{minipage}{0.5\textwidth}
\begin{code}
middle x y = (x + y) / 2
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{spec}
middle = \x -> \y -> (/) ((+) x y) 2
\end{spec}
\end{minipage}

In tegenstelling tot de lambda-calculus \TODO{Cite lambda-calculus?}, is Haskell
ook een \emph{sterk getypeerde} programmeertaal. Functies worden, naast een
definitie, ook voorzien van een \emph{type-signatuur}:

\begin{code}
middle :: Float -> Float -> Float
\end{code}

Net zoals lambda-abstracties is de |->| (een operator op type-niveau) in
type-signaturen rechts-associatief.  Deze type-signatuur is dus equivalent aan
|Float -> (Float -> Float)|. Dit concept heet \emph{currying}: we kunnen
|middle| beschouwen als een functie die \'e\'en Float argument neemt en functie
van het type |Float -> Float| als resultaatwaarde heeft, of als een functie die
twee |Float|-argumenten neemt en een |Float| als resultaatwaarde heeft.

In de lambda-calculus is het niet mogelijk om direct recursieve functies te
schrijven. Er bestaat echter een elegante oplossing: de
\emph{fixpoint-combinator}. Een fixpoint-combinator is een functie |g| waarvoor
geldt dat voor elke functie |f|: |g f = f (g f)|. Hierdoor is het mogelijk een
functie door te geven voor een recursieve oproep, zonder deze functie expliciet
een naam te geven.

E\'en van de de bekendste voorbeelden hiervan is de \emph{Y-combinator}.

\newtheorem{theorem:y-combinator}{Definitie}[section]
\begin{theorem:y-combinator}\label{theorem:y-combinator}
\[ |Y = \f -> (\x -> f (x x)) (\x -> f (x x))| \]
\end{theorem:y-combinator}

\newtheorem*{theorem:y-fixpoint}{Stelling}
\begin{theorem:y-fixpoint}\label{theorem:y-fixpoint}
|Y| is een fixpoint-combinator, dus:

\[ |Y f == f (Y f)| \]
\end{theorem:y-fixpoint}

\begin{proof}
~ \newline
\begin{spec}
    Y f

== {- def |Y| -}

    (\f -> (\x -> f (x x)) (\x -> f (x x))) f

== {- $\beta$-reductie -}

    (\x -> f (x x)) (\x -> f (x x)))

== {- $\beta$-reductie -}

    f ((\x -> f (x x)) (\x -> f (x x)))

== {- $\lambda$-abstractie -}

    f ((\f -> (\x -> f (x x)) (\x -> f (x x))) f)

== {- def |Y| -}

    f (Y f)
\end{spec}
\end{proof}

In tegenstelling tot de lambda-calculus is het in Haskell niet nodig om gebruik
te maken van fixpoint-combinators: men kan eenvoudig expliciet recursieve
definities geven door de functie zelf bij naam aan te roepen.

\begin{code}
fib :: Int -> Int
fib n = if n <= 1 then 1 else fib (n - 1) + fib (n - 2)
\end{code}

Verder breidt Haskell de lambda-calculus uit met \emph{algebra\"ische datatypes}
en \emph{pattern matching}. Een algebra\"isch datatype is in Haskell typisch een
\emph{somtype} (keuze tussen verschillende types) van \emph{producttypes}
(combinatie van verschillende types).

Beschouw het volgende voorbeeld:

\begin{code}
data Topping = Salami | Mozarella | Peppers

data Pizza
    =  Plain
    |  ExtraToppings Topping Topping
\end{code}

|Topping| is een somtype met drie verschillende constructoren zonder meer
informatie. |Pizza| is ook een somtype van twee verschillende constructoren,
waarvan \'e\'en een producttype is van twee |Topping|-types.

Met behulp van pattern-matching kan de onderliggende constructor onderzocht
worden:

\begin{code}
toppingPrice :: Topping -> Double
toppingPrice Salami     = 0.50
toppingPrice Mozarella  = 0.50
toppingPrice Peppers    = 0.30

pizzaPrice :: Pizza -> Double
pizzaPrice Plain                  = 5.20
pizzaPrice (ExtraToppings t1 t2)  = 5.40 + toppingPrice t1 + toppingPrice t2
\end{code}

Het zou ons te ver voeren om het volledig typesysteem van Haskell hier te
bespreken. We beperken ons dan ook tot de kenmerken die we nodig hebben in deze
scriptie. Een belangrijk en bijzonder interessant kenmerk van het typesysteem
dat we doorheen deze thesis gebruiken is \emph{type-polymorfisme}. Dit laat ons
toe om met \'e\'enzelfde set functies en datatypes te werken met waarden van
verschillende types. Beschouw bijvoorbeeld de identiteitsfunctie |id|. Deze
functie kan op een waarde van om het even welk type toegepast worden en is
bijgevolg polymorf.

\begin{code}
id :: a -> a
id x = x
\end{code}

Behalve polymorfe functies bestaan er ook polymorfe datatypes. Een voorbeeld
hiervan is de lijst: we kunnen voor elk mogelijk type een lijst maken met
waarden van dit type door de dezelfde constructoren |(:)| en |[]| te gebruiken.

\begin{spec}
data [a]
    =  a : [a]
    |  []
\end{spec}

Lijsten zijn alomtegenwoordig in functionele programma's en verdienen speciale
aandacht. Zo worden bijvoorbeeld |String|s in Haskell ook voorgesteld als
karakter-lijsten:

\begin{spec}
type String = [Char]
\end{spec}

Omdat een lijst een recursief datatype is, is het zeer gebruikelijk om
recursieve functies over lijsten te schrijven. Met behulp van de
standaard-functie |toUpper :: Char -> Char| kan men bijvoorbeeld een functie
schrijven die een volledige |String| omzet naar drukletters:

\begin{code}
upper :: String -> String
upper []        = []
upper (x : xs)  = toUpper x : upper xs
\end{code}

\section{Higher-order functies}

Omdat recursieve functies over lijsten alomtegenwoordig zijn, is het vaak
mogelijk patronen te onderscheiden. Beschouw even de volgende twee functies,
|sum| en |product|.

\begin{code}
sum :: [Int] -> Int
sum []        = 0
sum (x : xs)  = x + sum xs

product :: [Int] -> Int
product []        = 1
product (x : xs)  = x * product xs
\end{code}

Deze patronen kunnen ge\"implementeerd worden door middel van hogere-orde
functies: functies die andere functies als parameters nemen.  In het
bovenstaande voorbeeld zijn de functies eenvoudige voorbeelden van het |foldr|
patroon.

\begin{code}
foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _  z []        = z
foldr f  z (x : xs)  = f x (foldr f z xs)
\end{code}

Als we |sum| en |product| herschrijven op basis van |foldr|, krijgen we veel
beknoptere definities, die semantisch equivalent zijn aan de expliciet
recursieve versies en sneller te lezen door ervaren programmeurs:

\begin{code}
sum' :: [Int] -> Int
sum' = foldr (+) 0

product' :: [Int] -> Int
product' = foldr (*) 1
\end{code}

Andere voorbeelden van hogere-orde functies zijn |map| en |filter|. |map| laat
ons toe een functie uit te voeren op elk element van een lijst:

\begin{code}
map :: (a -> b) -> [a] -> [b]
map f = foldr (\x xs -> f x : xs) []

upper' :: String -> String
upper' = map toUpper
\end{code}

De |filter|-functie wordt gebruikt om bepaalde elementen uit een lijst te
selecteren:

\begin{code}
filter :: (a -> Bool) -> [a] -> [a]
filter f = foldr (\x xs -> if f x then x : xs else xs) []

odds :: [Int] -> [Int]
odds = filter odd
\end{code}

\section{De universele eigenschap van fold}
\label{section:universal-fold}

Het feit dat we zowel |map| als |filter| schrijven met behulp van |foldr| duidt
aan dat |foldr| een zeer interessante functie is. Meer bepaald, de universele
eigenschap van fold \cite{hutton1999} is weergegeven in stelling
\ref{theorem:universal-fold}.

\newtheorem{theorem:universal-fold}{Stelling}[section]
\begin{theorem:universal-fold}\label{theorem:universal-fold}
\[
  |g = foldr f v|
  ~~~~~~~ \Leftrightarrow
  \begin{minipage}[c]{0.30\textwidth}
  \begin{spec}
g []        = v
g (x : xs)  = f x (g xs)
  \end{spec}
  \end{minipage}
\]
\end{theorem:universal-fold}

Concreet betekent dit dat we een functie |g| kunnen herschrijven in termen van
|foldr| zodra we een |f| en |v| vinden die aan de bovenstaande voorwaarden
voldoen.

Ook betekent dit dat er slechts \'e\'en |foldr| is voor een lijst -- elke
alternatieve definitie is hieraan isomorf. Er is dus een wederzijds verband
tussen het type |[a]| en de functie |foldr|. De vraag naar het bestaan van een
bijectie tussen algebra\"ische datatypes en fold-functies dringt zich dus op.

Deze vraag kan affirmatief beantwoord worden: een dergelijke bijectie bestaat,
ze legt bovendien het verband tussen een datatype en het overeenkomstige
\emph{catamorfisme}: de unieke manier om een algebra\"isch datatype stap voor
stap te reduceren tot \'e\'en enkele waarde. We kunnen deze catamorfismes
eenvoudig afleiden voor algebra\"ische datatypes.

Om dit beter te verstaan, hebben we het concept van een \emph{algebra} nodig.
Wanneer we een catamorfisme toepassen op een datatype, interpreteren we dit
datatype in een bepaalde algebra, door elke constructor te vervangen door een
operator uit deze algebra. Zo is |sum| als het ware een interpretatie in de
som-algebra, die |(:)| en |[]| vervangt door respectievelijk |+| en |0|:

\begin{spec}
foldr (+) 0  (1  :  (2  :  (3  :  (4  :  []))))
==           (1  +  (2  +  (3  +  (4  +  0))))
\end{spec}

Dit idee laat ons toe folds te defini\"eren voor andere datatypes. Beschouw
bijvoorbeeld een eenvoudig boom-type:

\begin{code}
data Tree a
    =  Leaf a
    |  Branch (Tree a) (Tree a)
\end{code}

% For testing
\ignore{
\begin{code}
instance Show a => Show (Tree a) where
    show = foldTree
        (\x   -> "(Leaf " ++ show x ++ ")")
        (\l r -> "(Branch " ++ l ++ " " ++ r ++ ")")
\end{code}
}

Door een functie-argument te specificeren voor elke constructor, kunnen we nu
een fold defin\"eren voor het type |Tree|:

\begin{code}
foldTree  ::  (a -> b)       -- Operator voor leaf
          ->  (b -> b -> b)  -- Operator voor branch
          ->  Tree a         -- Input tree
          ->  b              -- Resultaat van de fold
foldTree leaf  _       (Leaf x)      = leaf x
foldTree leaf  branch  (Branch x y)  =
  branch (foldTree leaf branch x) (foldTree leaf branch y)
\end{code}

En met behulp van deze functie kunnen we dus eenvoudig recursieve functies over
bomen schrijven. |sumTree|, bijvoorbeeld, berekent de som van de waarden van de
bladeren van een boom:

\begin{code}
sumTree :: Tree Int -> Int
sumTree = foldTree id (+)
\end{code}

We concluderen dat een fold voor een bepaald algebra\"isch datatype dus
eenvoudig is af te leiden uit de definitie van dat datatype. Bijgevolg kunnen we
dit ook automatisch doen.

Template Haskell \cite{sheard2002} is een Haskell-extensie die toelaat om aan
type-safe compile-time meta-programmeren te doen. Op deze manier kunnen we
Haskell manipuleren met Haskell.

We implementeerden een algoritme in Template Haskell om de fold horende bij een
datatype automatisch te genereren. Zo kan bijvoorbeeld |foldTree| gegenereerd
worden door:

%{
%format quote = "~ ``"
\begin{spec}
$(deriveFold quote Tree "foldTree")
\end{spec}
%}

Het algoritme werkt als volgt. We gebruiken de types |Tree a| en |[a]| als
voorbeelden.

\begin{enumerate}

\item De fold neemt als laatste argument altijd een waarde van het opgegeven
type, en geeft een waarde van het type |b| terug.

\begin{spec}
foldTree  :: ... -> Tree a -> b
foldList  :: ... -> [a] -> b
\end{spec}

\item Per constructor wordt er een extra argument meegeven.

\begin{spec}
foldTree  :: <LeafArg> -> <BranchArg> -> Tree a -> b
foldList  :: <ConsArg> -> <NilArg> -> [a] -> b
\end{spec}

\item Wat zijn nu de concrete types van deze argumenten? Laten we eerst de types
van de constructoren beschouwen:

\begin{spec}
Leaf    :: a -> Tree a
Branch  :: Tree a -> Tree a -> Tree a

(:)   :: a -> [a] -> [a]
[]    :: [a]
\end{spec}

\item Deze constructoren geven de subtermen aan en corresponderen dus met de
verschillende argumenten. De recursie wordt echter afgehandeld door de |fold|
functie, en dus is elke recursieve subterm al gereduceerd tot een waarde van het
type |b|. Eveneens is |b| het type van het resultaat. We vinden:

\begin{spec}
<LeafArg>    = a -> b
<BranchArg>  = b -> b -> b

<ConsArg>  = a -> b -> b
<NilArg>   = b
\end{spec}

En dus:

\begin{spec}
foldTree  :: (a -> b) -> (b -> b -> b) -> Tree a -> b
foldList  :: (a -> b -> b) -> b -> [a] -> b
\end{spec}

\item Eenmaal de type-signaturen bepaald zijn is het genereren van de
implementatie redelijk eenvoudig. Elke functieparameter krijgt een naam naar de
constructor.  Vervolgens genereren we een |go| functie. Dit is een toepassing
van de Static Argument Transformation (zie \TODO{Cite SAT}).

\begin{spec}
foldTree :: (a -> b) -> (b -> b -> b) -> Tree a -> b
foldTree leaf branch = go
  where
    go (Leaf x)      = leaf x
    go (Branch x y)  = branch (go x) (go y)

foldList :: (a -> b -> b) -> b -> [a] -> b
foldList cons nil = go
  where
    go (x : y)  = cons x (go y)
    go []       = nil
\end{spec}

De |go| functie inspecteert simpelweg de constructor en roept dan het
corresponderende functie-argument met als argumenten de gereduceerde subtermen.
Een gereduceerde niet-recursieve subterm |t| is gewoon die subterm |t|, en voor
een recursieve subterm is dit |go t|.

\end{enumerate}

\section{Fusion: Folds en Builds}

\subsection{Wat is fusion?}

Naast de verschillende voordelen op vlak van \emph{refactoring}, is het ook
mogelijk \emph{optimalisaties} door te voeren op basis van deze hogere-orde
functions.

Beschouw de volgende twee versies van een functie die de som van de kwadraten
van de oneven nummers in een lijst berekent:

\begin{code}
sumOfSquaredOdds :: [Int] -> Int
sumOfSquaredOdds []  = 0
sumOfSquaredOdds (x : xs)
    | odd x          = x ^ 2 + sumOfSquaredOdds xs
    | otherwise      = sumOfSquaredOdds xs
\end{code}

\begin{code}
sumOfSquaredOdds' :: [Int] -> Int
sumOfSquaredOdds' = sum . map (^ 2) . filter odd
\end{code}

Ervaren Haskell-programmeurs zullen steevast de tweede versie boven de eerste
verkiezen. Het feit dat de tweede versie is opgebouwd uit kleinere, makkelijk te
begrijpen functies maakt deze veel leesbaarder.

De eerste versie is echter effici\"enter: deze berkent rechtstreeks het
resultaat (een |Int|), terwijl de tweede versie twee tijdelijke |[Int]| lijsten
aanmaakt: een eerste als resultaat van |filter odd|, en een tweede als resultaat
van |map (^ 2)|.

In de ideale situatie willen we dus de effici\"entie van de eerste versie
combineren met de leesbaarheid van de tweede versie. Dit wordt mogelijk gemaakt
door \emph{fusion} \cite{wadler1990} \cite{gill1993}.

We kunnen fusion best uitleggen aan de hand van een eenvoudig voorbeeld:
\emph{map/map-fusion}. Dit is een transformatie die gegeven wordt door stelling
\ref{theorem:map-map-fusion}.

\newtheorem{theorem:map-map-fusion}{Stelling}[section]
\begin{theorem:map-map-fusion}\label{theorem:map-map-fusion}
\[ |map f . map g| ~~ |==| ~~ |map (f . g)| \]
\end{theorem:map-map-fusion}

\begin{proof}
Deze equivalentie is eenvoudig te bewijzen via inductie.  We bewijzen dit eerst
voor de lege lijst |[]|. Voor |map f . map g| krijgen we:

\begin{spec}
    map f (map g [])

== {- def |map []| -}

    map f []

== {- def |map []| -}

    []

== {- def |map []| -}

    map (f . g) []
\end{spec}

We nemen nu aan dat map/map-fusion correct is voor een willekeurige lijst |xs|
en bewijzen dat de correctheid dan ook geldt voor een lijst |x : xs|.

\begin{spec}
    map f (map g (x : xs))

== {- def |map :| -}

    map f (g x : map g xs)

== {- def |map :| -}

    f (g x) : map f (map g xs)

== {- inductiehypothese -}

    f (g x) : map (f . g) xs

== {- def |map :| -}

    map (f . g) (x : xs)
\end{spec}
\end{proof}

GHC beschikt over een mechanisme om dit soort transformaties uit te voeren
tijdens de compilatie, door middel van het \verb|{-# RULES -#}| pragma's
\cite{jones2001}. Zo kunnen we bijvoorbeeld map/map-fusion implementeren door
eenvodigweg het volgende pragma te vermelden:

\begin{lstlisting}
{-# RULES "map/map-fusion" forall f g xs.
    map f (map g xs) = map (f . g) xs #-}
\end{lstlisting}

Het nadeel van deze aanpak is echter dat het aantal nodige rules kwadratisch
stijgt in proportie tot het aantal hogere-orde functies dat op het datatype (in
dit geval lijsten) werkt.

Ter illustratie, als we bijvoorbeeld enkel de twee functies |map| en |filter|
beschouwen, hebben al vier rules nodig, en een bijkomende hulpfunctie
|mapFilter|:

\begin{spec}
map f . map g        == map (f . g)
map f . filter g     == mapFilter f g
filter f . map g     == filter (f . g)
filter f . filter g  == filter (\x -> f x && g x)

mapFilter :: (a -> b) -> (a -> Bool) -> [a] -> [b]
mapFilter _ _ []  = []
mapFilter f g (x : xs)
    | g x         = f x : mapFilter f g xs
    | otherwise   = mapFilter f g xs
\end{spec}

Maar als we nu een langere expressie |map f . map g . filter h| hebben, kunnen
we iets krijgen als |map f . mapFilter g h|, en dienen we weer nieuwe
fusion-regels toe te voegen om deze expressie te kunnen fusen. Het aantal nodige
regels stijgt dus zeer snel.

Voor sommige modules ligt het aantal hogere-orde functies erg hoog, dus wordt
deze aanpak onhaalbaar.

\subsection{Foldr/build-fusion}
\label{subsection:foldr-build-fusion}

Dit probleem wordt opgelost met \emph{foldr/build-fusion}. We kunnen |foldr|
beschouwen als een algemene manier om lijsten te \emph{consumeren}. Hiervan is
|build| de tegenhanger: een algemene manier om lijsten te \emph{produceren}.

\begin{code}
build :: (forall b. (a -> b -> b) -> b -> b) -> [a]
build g = g (:) []
\end{code}

We kunnen nu bijvoorbeeld |map| en |filter| met behulp van |build| defini\"eren:

\begin{spec}
map :: (a -> b) -> [a] -> [b]
map f ls = build $ \cons nil ->
    foldr (\x xs -> cons (f x) xs) nil ls

filter :: (a -> Bool) -> [a] -> [a]
filter f ls = build $ \cons nil ->
    foldr (\x xs -> if f x then cons x xs else xs) nil ls
\end{spec}

Het nut van |build| wordt nu duidelijk: we gebruiken deze functie om te
\emph{abstraheren} over de concrete constructoren: in plaats van |(:)| en |[]|
gebruiken we nu de abstracte |cons| en |nil| parameters.

De type-signatuur van |build| met het expliciet universeel gekwantificeerde type
|b| is cruciaal. Stel dat dit niet het geval zou zijn, en dat we |build| zouden
defini\"eren met de meest algemene type-signatuur:

\begin{code}
build' :: ((a -> [a] -> [a]) -> [a] -> t) -> t
build' g = g (:) []
\end{code}

Dan zou code als |list123| well-typed zijn:

\begin{code}
list123 :: [Int]
list123 = build' $ \cons nil -> 1 : cons 2 (cons 3 [])
\end{code}

We krijgen een lijst die zowel gebruikt maakt van de concrete constructoren als
de abstracte versies. Dit leidt tot problemen: intu\"itief laten de abstracte
versies ons toe om de constructoren |(:)| en |[]| te \emph{vervangen} door
andere functies -- en zoals we in Sectie \ref{section:universal-fold} zagen,
kunnen we het toepassen van |foldr| net beschouwen als het vervangen van de
constructoren door de argumenten van |foldr|!

Als we echter ook nog letterlijk verwijzen naar |(:)| en |[]|, is deze
vervanging onmogelijk. Het universeel gekwantificeerde type |b| lost dit
probleem op. De programmeur is verplicht een |g| mee te geven die werkt voor
\emph{elke} |b|, en hij weet niet welk type uiteindelijk geconstrueerd zal
worden. Bijgevolg en kan hij dus ook geen concrete constructoren gebruiken.

Nu we vastgesteld hebben dat enkel de abstracte versies van de constructoren
gebruikt worden, laat dit idee ons toe om de productie en consumatie van een
lijst te fusen, zodanig dat er geen tijdelijke lijst moet worden aangemaakt. We
werken dit nu formeel uit.

\newtheorem{theorem:foldr-build-fusion}{Stelling}[section]
\begin{theorem:foldr-build-fusion}\label{theorem:foldr-build-fusion}
Als

\[ |g :: forall b. (A -> b -> b) -> b -> b| \]

dan

\[ |foldr cons nil (build g)| ~~ |==| ~~ |g cons nil| \]
\end{theorem:foldr-build-fusion}

\begin{proof} Van het type van een polymorfe functie kan een \emph{gratis
theorie} afgeleid worden \cite{wadler1989}. Zo krijgen we voor |g| dat voor alle
|f1|, |f2| en |h| met als types:

\begin{center}
\begin{spec}
h   :: B1 -> B2
f1  :: A -> B1 -> B1
f2  :: A -> B2 -> B2
\end{spec}
\end{center}

de volgende implicatie geldt:

\begin{align*}
(|forall x xs1 xs2. h xs1 == xs2| &\Rightarrow
        |h (f1 x xs1) == f2 x xs2|) \Rightarrow \\
(|forall xs1 xs2. h xs1 == xs2| &\Rightarrow
        |h (g f1 xs1) == g f2 xs2|)
\end{align*}

De gelijkheid |h xs1 == xs2| kunnen we tweemaal substitueren, waardoor de
implicatie herleid wordt tot:

\begin{align*}
(|forall x xs2. h (f1 x xs1)| & |== f2 x (h xs1)|) \Rightarrow \\
(|forall xs2. h (g f1 xs1)|   & |== g f2 (h xs1)|)
\end{align*}

We kunnen deze implicatie nu instanti\"eren met: |f1 := (:)|, |f2 := cons|, en
|h := foldr cons nil|. We krijgen dus:

\begin{align*}
(|forall x xs2. foldr cons nil (x : xs1)|  & |== cons x (foldr cons nil xs1)|)
    \Rightarrow \\
(|forall xs2. foldr cons nil (g (:) xs1)|  & |== g cons (foldr cons nil xs1)|)
\end{align*}

De linkerkant van de implicatie is triviaal geldig: dit is gewoon de definitie
van |foldr| voor een niet-ledige lijst. Hieruit volgt dat:

\[ |(forall xs2. foldr cons nil (g (:) xs2) == g cons (foldr cons nil xs2))| \]

Deze gelijkheid kunnen we opnieuw instanti\"eren, ditmaal met |xs2 := []|. Zo
krijgen we:

\begin{center}
\begin{spec}
    foldr cons nil (g (:) []) == g cons (foldr cons nil [])

== {- def |foldr []| -}

    foldr cons nil (g (:) []) == g cons nil

== {- def |build| -}

    foldr cons nil (build g) == g cons nil
\end{spec}
\end{center}

\end{proof}

Ter illustratie tonen we nu hoe met deze enkele fusion-regel onze elegantere
versie van |sumOfSquaredOdds'| automatisch door GHC kan worden omgezet naar een
performante versie.

\begin{spec}
    sumOfSquaredOdds'

== {- inline |sumOfSquaredOdds'| -}

    sum . map (^ 2) . filter odd

== {- inline |.| -}

    \ls -> sum (map (^ 2) (filter odd ls))

== {- inline |filter| -}

    \ls -> sum (map (^ 2)
        (build $ \cons nil ->
            foldr (\x xs -> if odd x then cons x xs else xs) nil ls))

== {- inline |map| -}

    \ls -> sum
        (build $ \cons' nil' ->
            foldr (\x xs -> cons' (x ^ 2) xs) nil'
                (build $ \cons nil ->
                    foldr (\x xs -> if odd x then cons x xs else xs) nil ls))

== {- foldr/build-fusion -}

    \ls -> sum
        (build $ \cons' nil' ->
            (\cons nil ->
                foldr (\x xs -> if odd x then cons x xs else xs) nil ls)
            (\x xs -> cons' (x ^ 2) xs)
            nil')

== {- $\beta$-reductie -}

    \ls -> sum
        (build $ \cons' nil' ->
            foldr (\x xs -> if odd x then cons' (x ^ 2) xs else xs) nil' ls)

== {- inline |sum| -}

    \ls -> foldr (+) 0
        (build $ \cons' nil' ->
            foldr (\x xs -> if odd x then cons' (x ^ 2) xs else xs) nil' ls)

== {- foldr/build-fusion -}

    \ls -> (\cons' nil' ->
        foldr (\x xs -> if odd x then cons' (x ^ 2) xs else xs) nil' ls) (+) 0

== {- $\beta$-reductie -}

    \ls -> foldr (\x xs -> if odd x then (x ^ 2) + xs else xs) 0 ls

\end{spec}

Uiteindelijk is |sumOfSquaredOdds'| dus volledig gereduceerd tot \'e\'en enkele
|foldr| over een lijst: het is niet meer nodig om tijdelijke lijsten te
alloceren om het resultaat te berekenen. In \TODO{Cite results chapter} tonen we
aan dat dit leidt tot significante versnellingen.

We krijgen dus als het ware het beste van beide werelden: we kunnen elegante
definities gebruiken voor de functies, die eenvoudiger leesbaar zijn en
makkelijker onderhoudbaar; maar tevens worden deze vertaald door de compiler tot
snelle, geoptimaliseerde versies.

\subsection{Foldr/build-fusion voor algebra\"ische datatypes}

In Sectie \ref{section:universal-fold} toonden we aan dat we een |fold| kunnen
defini\"eren voor om het even welk algebra\"isch datatype. Dit is ook mogelijk
voor |build|. Beschouw bijvoorbeeld een |build| voor ons |Tree|-datatype:

\begin{code}
buildTree :: (forall b. (a -> b) -> (b -> b -> b) -> b) -> Tree a
buildTree g = g Leaf Branch
\end{code}

Zodra we beschikken over een |fold| en een |build| voor een algebra\"isch
datatype, is het mogelijk om fusion toe te passen. Voor het type |Tree| wordt de
fusion-regel gegeven in definitie \ref{theorem:foldr-build-tree-fusion}.

\newtheorem{theorem:foldr-build-tree-fusion}{Definitie}[section]
\begin{theorem:foldr-build-tree-fusion}\label{theorem:foldr-build-tree-fusion}
\[ |foldTree leaf branch (buildTree g)| ~~ |==| ~~ |g leaf branch| \]
\end{theorem:foldr-build-tree-fusion}

Het bewijs hiervan verloopt analoog aan het bewijs voor
\ref{theorem:foldr-build-fusion} en wordt hier achterwege gelaten \TODO{Of moet
ik dit wel includeren? Het is 99\% hetzelfde...}.

Om dit te verduidelijken kunnen we kijken naar een concreet voorbeeld. Beschouw
de voorbeeldfunctie |treeUpTo| die een boom maakt met alle elementen van |n| tot
en met |m| in-order in de bladeren.

\begin{code}
treeUpTo :: Int -> Int -> Tree Int
treeUpTo n m = buildTree $ \leaf branch ->
    let g lo hi
            | lo >= hi   = leaf lo
            | otherwise  =
                let mid = (lo + hi) `div` 2
                in branch (g lo mid) (g (mid + 1) hi)
    in g n m
\end{code}

Nu kunnen we bestuderen wat er door fusion gebeurt met een expressie als
|sumTree (treeUpTo n m)|, die een tijdelijke boom aanmaakt.

\begin{spec}
    sumTree (treeUpTo n m)

== {- inline |sumTree| -}

    foldTree id (+) (treeUpTo n m)

== {- inline |makeTree| -}

    foldTree id (+) (buildTree $ \leaf branch ->
        let g lo hi
                | lo >= hi   = leaf lo
                | otherwise  =
                    let mid = (lo + hi) `div` 2
                    in branch (g lo mid) (g (mid + 1) hi)
        in g n m)

== {- foldTree/buildTree-fusion -}

    (\leaf branch ->
        let g lo hi
                | lo >= hi   = leaf lo
                | otherwise  =
                    let mid = (lo + hi) `div` 2
                    in branch (g lo mid) (g (mid + 1) hi)
        in g n m)
    id (+)

== {- $\beta$-reductie -}

    let g lo hi
            | lo >= hi   = id lo
            | otherwise  =
                let mid = (lo + hi) `div` 2
                in (g lo mid) + (g (mid + 1) hi)
    in g n m
\end{spec}

We krijgen een expressie die rechtstreeks de som uitrekent zonder ooit een
constructor te gebruiken. Opnieuw zal dit voor een significante versnelling
zorgen \TODO{Cite results chapter}.

Omdat naast |fold| ook |build| functies eenvoudig af te leiden zijn vanuit de
definitie van een datatype, hebben we dit ook geautomatiseerd. De programmeur
dient enkel nog |deriveBuild| op te roepen:

%{
%format quote = "~ ``"
\begin{spec}
$(deriveBuild quote Tree "buildTree")
\end{spec}
%}

Het algoritme om een |build| te genereren werkt als volgt:

\begin{enumerate}

\item De fold gebruikt een universeel gekwantificeerd type |b| in een functie
|g| en geeft een waarde terug van het opgegeven type.

\begin{spec}
buildTree :: (forall b. ... -> b) -> Tree a
buildTree g = elapsed

buildList  :: (forall b. ... -> b) -> [a]
buildList g = elapsed
\end{spec}

\item Opnieuw krijgen we voor elke constructor een functieparameter, ditmaal
voor |g|. De types voor deze functieparameters worden afgeleid op dezelfde
manier als in het algoritme voor |deriveFold| (zie Sectie
\ref{section:universal-fold}).

\begin{spec}
buildTree :: (forall b. (a -> b) -> (b -> b -> b) -> b) -> Tree a
buildTree g = elapsed

buildList  :: (forall b. (a -> b -> b) -> b -> b) -> [a]
buildList g = elapsed
\end{spec}

\item De implementatie bestaat vervolgens uit het toepassen van |g| op de
concrete constructoren.

\begin{spec}
buildTree :: (forall b. (a -> b) -> (b -> b -> b) -> b) -> Tree a
buildTree g = g Leaf Branch

buildList  :: (forall b. (a -> b -> b) -> b -> b) -> [a]
buildList g = g (:) []
\end{spec}

\end{enumerate}

\subsection{Foldr/foldr-fusion}

\TODO{Write this subsection}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Detectie folds}
\label{chapter:fold-detection}

\section{Notatie}

Om de tekst en regels in dit hoofdstuk en hoofdstuk
\ref{chapter:build-detection} eenvoudiger te maken, maken we geen gebruik van de
normale Haskell-syntax, noch GHC Core (zie sectie \ref{section:ghc-core}). In
plaats daarvan gebruiken we de simpele, ongetypeerde lambda-calculus, uitgebreid
met constructoren, pattern matching, en recursieve bindings.

Deze syntax wordt gegeven door:

% This table is copy-pasted from `draft.lhs`
\begin{center}
\begin{tabular}{llcl}
binding     & |b| & ::=  & |x = e|  \\
pattern     & |p| & ::=  & |K (many (x))| \\
expression  & |e| & ::=  & |x| \\
            &     & $\mid$ & |e e| \\
            &     & $\mid$ & |\x -> e| \\
            &     & $\mid$ & |K| \\
            &     & $\mid$ & |case e of many (p -> e)|
\end{tabular}
\end{center}

Het is eenvoudig te zien hoe we deze in de praktijk kunnen uitbreiden tot de
volledige GHC Core syntax.

Eveneens hebben we een \emph{context} nodig:

% Copy-pasta...
\begin{center}
\begin{tabular}{lcl}
|E| & ::=  & |x| \\
    & $\mid$ & |E x| \\
    & $\mid$ & |E box| \\
    & $\mid$ & |E triangle|
\end{tabular}
\end{center}

Een dergelijke context |E| doelt op een functie die toegepast wordt op een
aantal argumenten. De functie en 

% This figure is mostly copy-pasted from `draft.lhs` so we should update it
% accordingly. Changes:
%
% - `\begin{figure*}` -> `\begin{figure}`
% - Caption
% - Label
\begin{figure}[t]
\begin{center}
\fbox{
\begin{minipage}{0.95\textwidth}
\[\begin{array}{c}
\myruleform{\inferrule{}{b \leadsto b'}} \hspace{2cm}

\inferrule*[left=(\textsc{F-Bind})]
  { |e'1| = [|x| \mapsto |[]|]|e1| \\ |f| \not\in \mathit{fv}(|e'1|) \\\\ 
    |E|[|many u|;|y|] = |f (many x) y (many z)| \\ |ws|~\textit{fresh} \\\\ 
    |e2| \stackrel{E}{\leadsto}_{|ws|}^{|vs|} |e'2| \\ \{ f, x, vs \} \cap \mathit{fv}(|e'2|) = \emptyset
  }
  {
|f = \(many x) y (many z) -> case y of { [] -> e1 ; (v:vs) -> e2 }| \\\\
    \leadsto |f = \(many x) y (many z) -> foldr (\v ws (many u) -> e'2) (\many u -> e'1) y (many u)| 
  } \\
\\
\myruleform{\inferrule*{}{e~{}_x\!\!\stackrel{E}{\leadsto}_y~e'}} \hspace{2cm}
\inferrule*[left=(\textsc{F-Rec})]
  { e_i~{}_x\!\!\stackrel{E}{\leadsto}_y~e_i' \quad (\forall i)
  }
  { |E|[|many e|;|x|] ~{}_x\!\!\stackrel{E}{\leadsto}_y~|y (many e')|
  }
  \hspace{1cm}
\inferrule*[left=(\textsc{F-Refl})]
  {
  }
  { e~{}_x\!\!\stackrel{E}{\leadsto}_y~e
  }
 \\
\\
\inferrule*[left=(\textsc{F-Abs})]
  { |e|~{}_x\!\!\stackrel{E}{\leadsto}_y~|e'|
  }
  { |\z -> e|~{}_x\!\!\stackrel{E}{\leadsto}_y~|\z -> e'|
  }
  \hspace{0.5cm}
\inferrule*[left=(\textsc{F-App})]
  { |e1|~{}_x\!\!\stackrel{E}{\leadsto}_y~|e'1| \\
    |e2|~{}_x\!\!\stackrel{E}{\leadsto}_y~|e'2|
  }
  { |e1 e2|~{}_x\!\!\stackrel{E}{\leadsto}_y~|e'1 e'2|
  }
 \\
\\
\inferrule*[left=(\textsc{F-Case})]
  { |e|~{}_x\!\!\stackrel{E}{\leadsto}_y~|e'| \\ e_i~{}_x\!\!\stackrel{E}{\leadsto}_y~e_i' \quad (\forall i)
  }
  { |case e of many (p -> e)|~{}_x\!\!\stackrel{E}{\leadsto}_y~|case e' of many (p -> e')|
  } \\
\end{array} \]
\end{minipage}
}
\end{center}
\caption{De niet-deterministische regels die we gebruiken om mogelijke folds te
ontdekken en te herschrijven.}
\label{figure:fold-detection-rules}
\end{figure}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Detectie builds}
\label{chapter:build-detection}


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\chapter{Implementatie \& evaluatie}

\section{GHC Core}
\label{section:ghc-core}

Eerder beschreven we al \TODO{backreference} dat we voor deze thesis werken met
GHC \cite{ghc}, de de-facto standaard Haskell compiler.

GHC werkt met een \emph{kerneltaal}. Een kerneltaal is een gereduceerde subset
van de programmeertaal (in dit geval Haskell). Bovendien is het mogelijk om
elk Haskell-programma uit te drukken in de kerneltaal.

Een dergelijke vertaling gebeurt door de compiler en is beter bekend onder de
naam desugaring \footnote{De vele syntactische structuren die in idiomatische
Haskell-code gebruikt worden staan bekend als \emph{syntactic sugar}, vandaar
deze naam.}. Programmas die uitgedrukt worden in de kerneltaal zijn meestal
minder beknopt.

Het gebruik van een dergelijke kerneltaal heeft verschillende voordelen:

\begin{itemize}[topsep=0.00cm]

\item De syntax van de kerneltaal is zeer beperkt. Hierdoor kunnen de
programmeur en de compiler op een meer eenvoudige manier redeneren over
expressies, zonder rekening te houden met op dat moment oninteressante
syntactische details.

\item Om nieuwe syntax toe te voegen, dient men enkel het
\emph{desugaring}-proces aan te passen en hoeft men geen aanpassingen te doen in
de rest van de compiler.

\item Verschillende programmeertalen kunnen dezelfde kerneltaal delen. Dit laat
toe om bepaalde tools en optimalisaties \'e\'enmaal te schrijven en vervolgens
toe te passen voor programma's geschreven in verschillende programmeertalen. Dit
voordeel is echter niet van toepassing op GHC, omdat deze een eigen kerneltaal
gebruikt.

\end{itemize}

De kerneltaal van die GHC gebruikt heet GHC Core \cite{tolmach2009}.

Om onze fold- en build-detectie te implementeren hebben we dus twee keuzes. We
kunnen ofwel de Haskell-code direct manipuleren. Er bestaan reeds verschillende
bibliotheken om deze taak eenvoudiger te maken, zoals bijvoorbeeld
\emph{haskell-src-exts} \cite{haskell-src-exts}.

We kunnen echter ook werken met de GHC Core. Dit heeft voor ons een groot aandal
voordelen.

\begin{itemize}[topsep=0.00cm]

\item Zoals we eerder al vermeldden, is het syntax veel eenvoudiger. Dit drukt
zich ook uit in de complexiteit van de abstracte syntaxboom: Ter illustratie:
het |Expr|-type dat in \emph{haskell-src-exts} gebruikt wordt heeft 46
verschillende constructoren, terwijl het |Expr|-type van GHC Core er slechts 10
heeft.

\item De GHC Core gaat door verschillende optimalisatie-passes. Veel van deze
passes vereenvoudigen de expressies, wat op zijn beurt de analyse makkelijker
maakt. Beschouw bijvoorbeeld de volgende functie |jibble|:

\begin{code}
jibble :: [Int] -> Int
jibble []        = 1
jibble (x : xs)  = wiggle x xs

wiggle :: Int -> [Int] -> Int
wiggle x xs = x * jibble xs + 1
\end{code}

Hier is het moeilijk om een |foldr|-patroon te herkennen door het gebruik van de
hulpfunctie |wiggle|: onze implementatie gaat immers niet kijken wat de
definitie van |wiggle| is. Maar, eens deze functie ge-inlined is, krijgen we de
functie:

\begin{spec}
jibble :: [Int] -> Int
jibble []        = 1
jibble (x : xs)  = x * jibble xs + 1
\end{spec}

Onze detector kan de laatste versie onmiddelijk herkennen.

\item Tenslotte beschikken we ook over type-informatie: de GHC API laat ons toe
types van onder meer variabelen en functies op te vragen. Dit is in principe
niet essentieel voor onze detector, maar kan wel zeer nuttig zijn. Beschouw
bijvoorbeeld:

\begin{code}
add :: Int -> Int -> Int
add x y = elapsed
\end{code}

We kunnen, zonder de definitie van |add| te bekijken, al uit de type-signatuur
opmaken dat |add| geen |fold| noch |build| zal zijn. Het is immers niet mogelijk
te folden over een |Int| of er \'e\'en aan te maken met build: |Int| valt niet
in de klasse van de algebra\"ische datatypes.

\end{itemize}

We dienen wel op te merken dat er ook een belangrijk nadeel gekoppeld is aan het
werken met GHC Core in plaats van Haskell code. Het wordt namelijk veel
moeilijker om de resultaten van onze analyse te gebruiken voor
\emph{refactoring}.

In dit geval zouden we de originele code willen herschrijven onder de vorm van
een fold of een build. Dit vereist echter een geannoteerde abstracte syntaxboom
die toelaat om expressies uit GHC Core terug te koppelen naar Haskell
expressies, inclusief alle syntactische sugar waar de programmeur gebruik van
kan maken. Automatisch herschrijven van expressies in GHC Core zorgt dan voor
een soortgelijke update van de corresponderende Haskell code. Deze stap valt
echter buiten het huidig bereik van deze thesis. We gaan hier iets dieper op in
sectie \TODO{future work}.

Om bovenstaande redenen kiezen we er dus voor om met GHC Core te werken. In
Figuur \ref{figure:haskell-to-ghc-core} geven we een kort overzicht van de
omzetting van Haskell-expressies naar de corresponderende expressies in GHC
Core.

\begin{figure}[h]
  \begin{tabular}{ll}
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    "Jan"
    \end{spec}
    \end{minipage} &
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    ((:) 'J' ((:) 'a' ((:) 'n' )))
    \end{spec}
    \end{minipage} \\

    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    head []       = undefined
    head (x : _)  = x
    \end{spec}
    \end{minipage} &
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    head = \xs -> case xs of
        []       -> undefined
        (:) x _  -> x
    \end{spec}
    \end{minipage} \\

    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    let  x  = 3
         y  = 4
    in x + y + z
    where z = 5
    \end{spec}
    \end{minipage} &
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    let z = 5
    in  let x = 3
        in  let y = 4
            in (+) x ((+) y z)
    \end{spec}
    \end{minipage} \\

    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    compare a b
      | a > b      = GT
      | a == b     = EQ
      | otherwise  = LT
    \end{spec}
    \end{minipage} &
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    compare = \a -> \b ->
      case (>) a b of
        True   -> GT
        False  -> case (==) a b of
          True   -> EQ
          False  -> LT
    \end{spec}
    \end{minipage} \\

    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    foldM f a []        = return a
    foldM f a (x : xs)  = do
      a' <- f a x
      foldM f a' xs
    \end{spec}
    \end{minipage} &
    \begin{minipage}{0.4\textwidth}
    \begin{spec}
    foldM = \f a ls -> case ls of
      []        -> return a
      (:) x xs  ->
        f a x >>= \a' -> foldM f a' xs
    \end{spec}
    \end{minipage} \\
  \end{tabular}
  \caption{Een overzicht van hoe Haskell-expressies worden omgezet naar
  GHC Core-expressies. Links worden de Haskell-expressies getoond, en rechts de
  overeenkomstige GHC Core-expressies}
  \label{figure:haskell-to-ghc-core}
\end{figure}

\section{Het GHC Plugins systeem}
\label{section:ghc-plugins-system}

Nu we beslist hebben op het niveau van GHC Core te werken, dringt zich de vraag
op hoe we deze GHC Core-expressies kunnen manipuleren.

De vraag is nu hoe we deze GHC Core kunnen manipuleren. Tot voor kort was dit
enkel mogelijk door de source code van GHC direct aan te passen.

Om aan dit probleem tegemoet te komen werd een nieuw pluginsysteem
ge\"introduceerd \cite{ghc-plugins} in GHC 7.2.1, dat de praktische kant van een
dergelijke manipulatie behoorlijk vereenvoudigt.

Meer bepaald is het nu mogelijk om Core-naar-Core tranformaties te implementeren
in aparte modules, en deze vervolgens mee te geven aan GHC via commmand-line
argumenten.

De module moet een |plugin :: Plugin| definitie bevatten.

\begin{code}
plugin :: Plugin
plugin = defaultPlugin {installCoreToDos = install}
\end{code}

De |installCoreToDos| laat toe om de lijst van passes aan te passen. Dit is een
standaard Haskell-lijst en bevat initi\"eel alle passes die GHC traditioneel
uitvoert. Met |intersperse| kunnen we bijvoorbeeld onze passes laten uitvoeren
tussen elke twee GHC-passes.

\begin{code}
install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _options passes = return $ intersperse myPlugin passes
  where
    myPlugin = CoreDoPluginPass "My plugin" (bindsOnlyPass myPass)
\end{code}

De implementatie van de effectieve pass heeft typisch de type-signatuur
|CoreProgram -> CoreM CoreProgram|. Hierin kunnen we dus gemakkelijk de
expressies bewerken, gelet op het feit dat ze worden voorgesteld als een
algebra\"isch datatype.

\begin{code}
myPass :: CoreProgram -> CoreM CoreProgram
myPass = elapsed
\end{code}

We illustreren hier een vereenvoudigde versie van het algebra\"isch datatype dat
door GHC gebruikt wordt:

\begin{spec}
type CoreProgram = [Bind Var]

data Bind b
    =  NonRec b Expr
    |  Rec [(b, Expr)]

data Expr b
    =  Var Id
    |  Lit Literal
    |  App (Expr b) (Expr b)
    |  Lam b (Expr b)
    |  Let (Bind b) (Expr b)
    |  Case (Expr b) b Type [Alt b]
    |  Cast (Expr b) Coercion
    |  Tick (Tickish Id) (Expr b)
    |  Type Type
    |  Coercion Coercion

type Alt b = (AltCon, [Id], Expr b)
\end{spec}

|Var| stelt eenvoudigweg variabelen voor, en literals worden door |Lit|
geconstrueerd. |App| en |Lam| zijn respectievelijk lambda-applicatie en
lambda-abstractie, concepten waarmee we bekend zijn uit de lambda-calculus.
|Let| stelt |let|-expressies voor, zowel recursief als niet-recursief. |Case|
stelt |case|-expressies voor maar heeft meerdere parameters: een extra binder
voor de expressie die onderzocht wordt door de |case|-expressie (ook de
\emph{scrutinee} genoemd), en het type van de resulterende alternatieven.
|Cast|, |Tick|, |Type| en |Coercion| worden gebruikt voor expressies die niet
relevant zijn voor het onderwerp van deze thesis. We gaan hier dus niet dieper
op in.

Haskell-programma's worden door de compiler voorgesteld in een dergelijke
abstracte syntaxboom, en plugins kunnen deze bomen manipuleren om de gewenste
transformatie uit te voeren. De syntaxbomen voor de belangrijkste GHC
Core-expressies worden getoond in Figuur \ref{figure:ghc-core-ast}.

\begin{figure}[h]
  \begin{tabular}{ll}
    |x| \hspace{0.40\textwidth} &
    |Var "x"| \\

    |2| &
    |Lit 2| \\

    |e1 e2| &
    |App e1 e2| \\

    |\x -> e| &
    |Lam x e| \\

    |let x = e1 in e2| &
    |Let (NonRec x e1) e2| \\

    |case e1 of C x1 x2 -> e2| &
    |Case e1 _ _ [(DataCon C, [x1, x2], e2)]| \\
  \end{tabular}
  \caption{Een overzicht van hoe GHC-Core expressies worden voorgesteld in de
  abstracte syntaxboom.}
  \label{figure:ghc-core-ast}
\end{figure}

Ter illustratie beschouwen we een plugin pass die zorgt voor het inlinen van
niet-recursieve binds. Een dergelijke pass zorgt dus voor een transformatie van
|let x = e1 in e2| naar |subst e2 x e1|.

\begin{code}
simpleBetaReduction :: CoreProgram -> CoreM CoreProgram
simpleBetaReduction = return . map (goBind [])
  where
    goBind :: [(Var, Expr Var)] -> Bind Var -> Bind Var
    goBind env (NonRec x e)  = NonRec x (go ((x, e) : env) e)
    goBind env (Rec bs)      = Rec [(x, go env e) | (x, e) <- bs]

    go :: [(Var, Expr Var)] -> Expr Var -> Expr Var
    go env (Var x)                 =
        case lookup x env of Nothing -> Var x; Just e -> (go env e)
    go env (Lit x)                 = Lit x
    go env (App e1 e2)             = App (go env e1) (go env e2)
    go env (Lam x e)               = Lam x (go env e)
    go env (Let (NonRec x e1) e2)  = go ((x, e1) : env) e2
    go env (Let (Rec bs) e2)       =
        Let (Rec [(x, go env e1) | (x, e1) <- bs]) (go env e2)
    go env (Case e1 x1 ty alts)    =
        Case (go env e1) x1 ty
            [(ac, bnds, go env e2) | (ac, bnds, e2) <- alts]
    go env (Cast e c)              = Cast (go env e) c
    go env (Tick t e)              = Tick t (go env e)
    go env (Type t)                = Type t
    go env (Coercion c)            = Coercion c
\end{code}

\TODO{Uitleg of update over shadowing}

Eenmaal een dergelijke plugin geschreven is, kan ze eenvoudig gebruikt worden.
Hiervoor gaan we als volgt te werk. Eerst \emph{packagen} we de plugin met
\emph{cabal} \cite{cabal} en installeren we ze:

\begin{lstlisting}
cabal install my-plugin
\end{lstlisting}

Vervolgens kan men door slechts enkele commandolijn-argumenten mee te geven GHC
opdragen dat deze plugin geladen en uitgevoerd moet worden tijdens de
compilatie:

\begin{lstlisting}
ghc --make -package my-plugin -fplugin MyPlugin test.hs
\end{lstlisting}

Waarbij |MyPlugin| de module is die |plugin :: Plugin| bevat. \texttt{my-plugin}
is de naam van het ge\"installeerde cabal-package. Dit toont aan dat het
relatiev eenvoudig is om GHC uit te breiden of aan te passen met behulp van het
plugin framework. Bovendien hoeven we geen GHC code aan te passen, zolang de
vereiste transformaties op de abstracte syntaxbomen kunnen uitgevoerd worden.

\section{De what-morphism plugin}

Voor deze thesis ontwikkelden we een GHC plugin genaamd \emph{what-morphism}
\cite{what-morphism}. Er zijn vier passes ge\"implementeerd in deze plugin,
alhoewel ze niet alle vier gebruikt worden.

\begin{itemize}[topsep=0.00cm]

\item |WhatMorphism.Fold|: conversie van expliciete recursie naar een functie in
termen van een fold.

\item |WhatMorphism.Build|: herschrijven van functies die gebruik maken van
expliciete constructoren, naar functies die |build| te gebruiken.

\item |WhatMorphism.Inliner|: een extra inliner die beter aanstuurbaar is in
vergelijking met de GHC inliner.

\item |WhatMorphism.Fusion|: een implementatie van de foldr/build-fusion die
werkt voor alle datatypes zonder dat er extra \verb|{-# RULES #-}| pragma's
nodig zijn.

\end{itemize}

De passes werken op basis van een best-effort en kunnen dus falen voor bepaalde
expressies. Dit betekent niet dat de compilatie wordt afgebroken, wel dat we de
transformatie niet kunnen maken en dus de originele expressie behouden.

\subsection{Annotaties}
\label{subsection:annotations}

\TODO{write here}

\begin{lstlisting}
{-# ANN type Tree (RegisterFoldBuild "foldTree" "buildTree") #-}
\end{lstlisting}

\subsection{WhatMorphism.Fold}

De |WhatMorphism.Fold| pass is een meer deterministische implementatie van de
regels in \TODO{Cite regels}.

We gebruiken de volgende functie ter illustratie (hier voorgesteld als
Core-expressie):

\begin{code}
foldlTree :: (a -> b -> a) -> a -> Tree b -> a
foldlTree = \f z0 tree ->
    let go = \z -> \t -> case t of
            Leaf x      -> f z x
            Branch l r  -> let z' = go z l in go z' r
    in go z0 tree
\end{code}

Dit is een \emph{left fold} over een |Tree| (gedefini\"eerd in sectie
\ref{section:universal-fold}.

Net zoals een left fold over een lijst, |foldl| kan uitgedrukt worden in functie
van |foldr|, kan dit ook voor andere algebra\'isch datatypes, zoals |Tree|.

Om folds te detecteren, is het nuttig om elke |Bind| in het programma te
bestuderen. Dit laat ons toe om mogelijke folds te vinden zowel in
\emph{top-level} binds alsook in lokale |let|- of |where|-binds. In ons vorbeeld
kunnen we de |go| uit de |let|-bind omvormen tot een fold.

We volgen de volgende stappen om de recursieve |go| om te vormen tot een
expressie die gebruikt maakt van een fold:

\begin{enumerate}[topsep=0.00cm]

\item We beginnen met alle argumenten van de bind te verzamelen in een lijst en
we kijken of er dan een |Case| volgt in de syntaxboom. We kunnen nu de
argumenten rangschikken als volgt: het \emph{scrutinee}-argument (het argument
dat wordt afgebroken door de |Case|, type-argumenten, en bijkomende argumenten.

De bijkomende argumenten partitioneren we in twee klasses: verandelijke en
statische argumenten. Een statisch argument is een argument dat hetzelfde is in
elke oproep, zoals we eerder in \TODO{ref} bespraken.  Type-argumenten dienen we
ook op een andere manier te behandelen, maar hier gaan we niet dieper op in.

In ons voorbeeld vinden we dat de boom |t| het scrutinee-argument is, en |z| een
veranderlijk bijkomend argument.

\item In de |fold| zal het niet meer mogelijk zijn om rechtstreeks te verwijzen
naar |t|. Daarom vervangen we in de rechterleden van de |Case|-alternatieven
telkens |t| door de linkherhandzijde van het alternatief.  Voor |go| hebben we
dus bijvoorbeeld voor het eerste alternatief |subst ((f z x)) t (Leaf x)|.

\item Vervolgens bestuderen we de expressies in de rechterleden van de
verschillende |Case|-alternatieven. Het is de bedoeling deze alternatieven te
herschrijven naar anonieme functies, zodat ze als argumenten voor de fold kunnen
dienen.

De argumenten voor deze anonieme functies zijn de binders van het alternatief
gevolgd door de verandelijke bijkomende argumenten. Zo krijgen we in ons
voorbeeld |\x z -> elapsed| en |\l_rec r_rec z -> elapsed| \footnote{Het
|_rec|-suffix duidt hier op het feit dat dit niet de originele binders zijn,
aangezien het type veranderde. Dit is een implementatie-detail, dat verder geen
invloed heeft op de essentie van het algoritme.}.

We construeren dan verder deze anonieme functies door te vertrekken vanuit de
rechterleden van de alternatieven en hierin expliciete recursie te elimineren.
Wanneer we zo'n expliciete recursie vinden, kijken we welk argument er op de
plaats van de scrutinee staat.

Als onze functie daadwerkelijk een |fold| is, zal dit altijd een recursieve
subterm van het datatype zijn: een |fold| zal altijd de recursieve subtermen op
een recursieve manier reduceren. Indien er een ander argument op de plaats van
de scrutinee staat, kunnen we het algoritme stopzetten, omdat de functie geen
fold is. Anders herschrijven we de recursieve oproep als de nieuwe binder voor
de recursieve subterm toegepast op de veranderlijke bijkomende argumenten.

In ons voorbeeld krijgen we dus:

\begin{minipage}[c]{0.40\textwidth}
\begin{spec}
    Leaf x      -> f z x
    Branch l r  ->
        let z' = go z l in go z' r
\end{spec}
\end{minipage}
$\Leftrightarrow$
\begin{minipage}[c]{0.40\textwidth}
\begin{spec}

\x z            -> f z x
\l_rec r_rec z  ->
    let z' = l_rec z in r_rec z'
\end{spec}
\end{minipage}

We zien aldus hoe op deze manier verandelijke bijkomende argumenten als |z|
worden doorgegeven.

\item Tenslotte dienen we de anonieme functies aan de argumenten van de |fold|
te koppelen: dat doen we in de implementatie simpelweg door de volgorde van de
constructoren op te vragen en te herordenen naar de volgorde van de argumenten
van de |fold| (|foldTree| in dit geval). We geven natuurlijk ook de scrutinee
mee als laatste argument voor deze |fold|, gevolgd door de bijkomende
argumenten, zodat deze kunnen worden doorgegeven aan verdere oproepen.

We krijgen dus:

\begin{code}
foldlTree' :: (a -> b -> a) -> a -> Tree b -> a
foldlTree' = \f z0 tree ->
    foldTree
        (\x z -> f z x)
        (\l_rec r_rec z -> let z' = l_rec z in r_rec z')
        tree
        z0
\end{code}

\end{enumerate}

\subsection{WhatMorphism.Build}

|WhatMorphism.Build| is de pass die ervoor verantwoordelijk is om functies die
waarden construeren met concrete constructoren, om te zetten naar functies die
gebruik maken van de build voor het corresponderende datatype.

We gebruiken ook hier ook meer determintisch algoritme dan de
niet-deterministische regels voorgesteld in \TODO{backref}. Als voorbeeld
gebruiken we de functie |infiniteTree|:

\begin{code}
infiniteTree :: Tree Int
infiniteTree =
    let go = \n -> Branch (Leaf n) (go (n + 1))
    in go 1
\end{code}

We zoeken overal naar functies die we kunnen omzoeken, dus zowel in top-level
definities (|infiniteTree|) als lokale definities (|go|). In dit geval kan |go|
geschreven worden in termen van |buildTree|. Het algoritme verloopt als volgt:

\begin{enumerate}[topsep=0.00cm]

\item We kijken naar het type van de functie in kwestie en bepalen aan hand
daarvan het return-type. In dit geval krijgen hebben we |go :: Int -> Tree Int|
en dus is |Tree Int| ons return-type.

Let erop dat zoals we in sectie \ref{section:haskell-types-and-functions}
opmerkten, Haskell type-signaturen op verschillende manieren kunnen gelezen
worden. Bij een functie als |f :: Int -> Int -> Tree Int| kunnen we zowel |Int
-> Tree Int|, |Tree Int| (en in principe ook |Int -> Int -> Tree Int|) als
type-signatuur beschouwen. Dit vormt echter geen probleem: aangezien er geen
build bestaat voor functietypes (deze types hebben geen constructoren) dienen we
altijd voor |Tree Int| te kiezen.

\item In subsectie \ref{subsection:annotations} bespraken we de annotaties die
GHC toelaat voor types. Hierdoor is het op dit moment mogelijk om, naast
allerlei info over het datatype (welke constructoren zijn er?) ook de bijhorende
build-functie op te vragen.

We maken nu een nieuwe functie |g| aan die dezelfde argumenten neemt als de
functie in kwestie maar een meer generiek return-type heeft: een vrije variabele
|b|. In ons voorbeeld:

\begin{spec}
go  :: Int -> Tree Int
g   :: Int -> b
\end{spec}

Uit de type-signatuur van de build kunnen we vervolgens de verschillende
argumenten afleiden:

\begin{spec}
leaf    :: a -> b
branch  :: b -> b -> b
\end{spec}

Op dit moment hebben we dus genoeg informatie om een skelet-functie te
construeren die er voor ons voorbeeld uitziet als:

\begin{spec}
infiniteTree :: Tree Int
infiniteTree =
    let go = \n -> buildTree $ \leaf branch ->
            let g = \n' -> elapsed
            in g n
    in go 1
\end{spec}

\item We kunnen nu afdalen in de definitie van |go| en deze herschrijven naar de
functie |g|. Om dit te doen bestuderen we de return-waarde van |go|. We
onderscheiden drie gevallen:

\begin{itemize}[topsep=0.00cm]

\item Er is sprake van directe recursie naar |go|. Dit kunnen we toelaten, al
moeten we dit natuurlijk herschrijven naar directe recursie naar |g| zodat de
functie well-typed blijft.

\item De return-waarde is een oproep naar de build-functie. Dit is uiteraard
toegelaten, aangezien deze return-waarde ook de abstracte versies van de
constructoren zal gebruiken. We dienen er wel voor te zorgen dat dezelfde
variabelen gebruikt worden, hiertoe geven we ze gewoon als argumenten aan de
|g'| van de geneste build. M.a.w., we herschrijven bijvoorbeeld:

\begin{spec}
build $ \leaf branch -> build g'
\end{spec}

Naar:

\begin{spec}
build $ \leaf branch -> g' leaf branch
\end{spec}

\item Tenslotte is het uiteraard ook toegelaten de return-waarde te construeren
met de concrete constructoren (in ons voorbeeld |Leaf| en |Branch|). Deze
vervangen we dan door de abstracte versies (in ons voorbeeld |leaf| en
|branch|). We moeten echter wel opletten als een constructor direct recursieve
subtermen bevat (bijvoorbeeld |Branch|): daarbij passen we dezelfde drie
gevallen opnieuw toe, maar dan op de subterm.

\end{itemize}

Na toepassing van deze regels krijgen we:

\begin{spec}
infiniteTree :: Tree Int
infiniteTree =
    let go = \n -> buildTree $ \leaf branch ->
            let g = \n' -> branch (leaf n') (g (n' + 1))
            in g n
    in go 1
\end{spec}

Met |go| een functie die herschreven is zodanig dat deze eventueel later kan
genieten van foldr/build-fusion.

\end{enumerate}

\subsection{WhatMorphism.Inliner}

Zoals we later ook in subsectie \ref{subsection:to-inline-or-not-to-inline}
zullen zien, is het niet altijd eenvoudig om te beslissen of een functie wel
dan niet moet worden ge-inlined.

Daarom implementeerden we eerst een eigen inliner die alle functies die we reeds
omgezet hebben altijd inlinet. Dit bleek echter niet altijd tot goede resultaten
te leiden, zoals ook in subsectie \ref{subsection:to-inline-or-not-to-inline} te
lezen is. Uiteindelijk kozen we er dus voor om zo goed mogelijk te proberen
samenwerken met de GHC inliner via de pragma's die beschikbaar zijn.

\subsection{WhatMorphism.Fusion}

Zoals we reeds in subsectie \ref{subsection:foldr-build-fusion} zagen, bestaat
foldr/build-fusion eruit door met de volgende regel het patroon in de linkerlid
van de stelling te vervangen door het patroon in het rechterlid:

\[ |foldr cons nil (build g) == g cons nil| \]

We kunnen dit doen met behulp van een \verb|{-# RULES #-}| pragma. Dit ziet er
dan als volgt uit:

\begin{lstlisting}
{-# RULES "foldr/build-fusion"
    forall c n (g :: forall b. (a -> b -> b) b -> -> b).
    foldHaskellList c n (buildHaskellList g) = g c n #-}
\end{lstlisting}

Een dergelijke regel moet worden toegevoegd voor \emph{elk} datatype waarvoor we
fusion willen:

\begin{lstlisting}
{-# RULES "foldTree/buildTree-fusion"
    forall l n (g :: forall b. (a -> b) -> (b -> b -> b) -> b) .
    foldTree l n (buildTree g) = g l n #-}
\end{lstlisting}

Door het expliciet gekwantificeerde type van |g| zijn deze regels erg verboos.
Om dit te verhinderen stellen we twee mogelijkheden voor:

\begin{itemize}[topsep=0.00cm]

\item Een Template Haskell functie die de \verb|{-# RULES #-}| pragma genereerd;

\item Een extra pass, |WhatMorphism.Fusion|, die het fusion-patroon op een
generieke manier implementeerd.

\end{itemize}

We implementeerden beide oplossingen. De Template Haskell functie kan als volgt
aangeroepen worden:

%{
%format quote = "~ ``"
\begin{spec}
$(deriveFold quote Tree "foldTree" "buildTree")
\end{spec}
%}

En deze genereerd dan de bovenstaande |"foldTree/buildTree-fusion"| regel.

De |WhatMorphism.Fusion| pass neemt een andere aanpak. Door gebruik te maken van
de reeds aanwezige annotaties (zie subsectie \ref{subsection:annotations}),
kunnen we voor elke variabele die gebruikt wordt eenvoudig nagaan of dit al dan
niet een fold of een build is voor een bepaald algebra\"isch datatype.

Het concrete algoritme gaat als volgt:

\begin{enumerate}[topsep=0.0cm]

\item We doorzoeken alle expressies naar variabelen waarvan we weten dat ze een
|fold| zijn voor een bepaald algebra\"isch datatype.

\item Vervolgens kunnen we de nodige informatie ophalen over dit datatype. Zo
dienen we te weten hoeveel constructor-argumenten de fold heeft. De
constructor-argumenten worden gevolgd door de waarde waarover de fold loopt. Als
we niet genoeg argumenten hebben, stoppen we op dit moment met het algoritme.

\item We kijken of het laatste argument van de fold (de waarde waarover de fold
loopt) een build is voor hetzelfde datatype. Als dit het geval is, hoeven we nu
slechts het |g|-argument van de build te nemen, en dit vervolgens toepassen op
de constructor-argumenten van de fold.

\end{enumerate}

Alhoewel beide aanpakken min of meer hetzelfde doen, kiezen we er voor om de
tweede aanpak, een |WhatMorphism.Fusion| pass te gebruiken. Hierover hebben we
immers iets meer controle, zo breidden we deze pass al uit zodanig dat er door
|let|-bindings kan gekeken worden. Ook kunnen we op deze manier voor iets meer
debug-output zorgen waardoor we eenvoudiger kunnen zien waarom de fusion wel of
niet wordt toegepast.

\section{Aanpassen van de compilatie-passes}

\subsection{Volgorde van de passes}

Zoals eerder besproken in sectie \ref{section:ghc-plugins-system}, kan onze
plugin, op het moment dat deze geladen wordt, de passes die GHC zal uitvoeren
wijzigen. We kunnen natuurlijk bijvoorbeeld na\"ief onze plugins als eerste
runnen, maar om goede resultaten te boeken, blijkt het uitermate belangrijk de
plugins optimaal te laten samenwerken met GHC.

Ten eerste willen we geen enkele GHC-phase verwijderen: anders beginnen we
onmiddelijk met een nadeel tegenover de standaard lijst van passes. Om maximaal
resultaat te boeken, runnen we onze reeks plugins telkens tussen elke twee GHC
passes, en wel in deze volgorde:

\begin{enumerate}[topsep=0.00cm]

\item Eerst voeren we |WhatMorphism.Build| uit. Het is belangrijk dat we eerst
functies naar builds omzetten en vervolgens pas naar folds. Beschouw het
volgende voorbeeld om dit te illustreren:

\begin{spec}
upper :: String -> String
upper []        = []
upper (x : xs)  = toUpper x : upper xs
\end{spec}

We kunnen dit eerst naar een build omzetten met ons algoritme:

\begin{spec}
upper :: String -> String
upper str = build $ \cons nil ->
    let g str' = case str' of
            []        -> nil
            (x : xs)  -> cons (toUpper x) (g xs)
    in g str
\end{spec}

En vervolgens naar een fold:

\begin{spec}
upper :: String -> String
upper str = build $ \cons nil ->
    let g str' = foldr (\x xs -> cons (toUpper x) xs) nil str'
    in g str
\end{spec}

Beide omzettingen zijn succesvol en nu kan de functie |upper| zowel als
producent als consument van een lijst van foldr/build-fusion genieten.

Stel dat we echter eerst |WhatMorphism.Fold| zouden uitvoeren:

\begin{spec}
upper :: String -> String
upper = foldr (\x xs -> toUpper x : xs) []
\end{spec}

Dit werkt, maar vervolgens zal |WhatMorphism.Build| dit niet meer kunnen
omzetten naar een build: ons algoritme is niet in staat om te zien dat |foldr|
enkel de constructoren |(:)| en |[]| zal gebruiken. In dit geval kan |upper| dus
enkel als consument van een lijst van foldr/build-fusion genieten.

Daaruit kunnen we concluderen dat het voordelig is om eerst |WhatMorphism.Build|
uit te voeren en daarna pas |WhatMorphism.Fold|.

\TODO{Alternatief: fold-regel wanneer we naar build omzetten}

\item Vervolgens voeren we |WhatMorphism.Fold| uit, vanwege de bovenstaande
redenen.

\item Voor functies die we succesvol omzetten naar folds en builds, passen we de
\emph{inliner-info} aan. Dit zorgt ervoor dat GHC deze agressief zal proberen
inlinen. Dit is nodig om aan foldr/build-fusion te doen, aangezien deze pass
enkel de fold- en build-functies herkent, en niet bijvoorbeeld functies
geschreven in termen van fold en build.

Het is dus geen goed idee om nu al |WhatMorphism.Fusion| uit te voeren,
aangezien het zeer onwaarschijnlijk is dat deze iets zal kunnen herkennen.

In plaats daarvan voeren we nu dus een bijkomende |Simplifier| pass uit met
|sm_inline = True|: dit geeft een goede kans om nodige functies te inlinen.

\item Tenslotte kunnen we de |WhatMorphism.Fusion| pass uitvoeren.

\end{enumerate}

\subsection{Inlinen of niet inlinen?}
\label{subsection:to-inline-or-not-to-inline}

Een andere belangrijke vraag is of we de functies |foldr| en |build| (en
natuurlijk de andere folds en builds die we genereren voor bijkomende
algebra\"ische datatypes) willen inlinen. Het antwoord is geen eenvoudige ja of
nee, aangezien beide keuzes voordelen en nadelen hebben.

Indien we de functies niet zouden inlinen, met een \verb|{-# NOINLINE #-}|
pragma, kunnen we meer foldr/build-fusion instanties detecteren: zodra \'e\'en
van deze functies ge-inlined wordt, voldoen ze immers niet meer aan het patroon
dat we herkennen.

Inlinen met een \verb|{-# INLINE #-}| pragma zorgt echter wel voor snellere code
omdat de functiecall-overhead vermeden wordt.

Het is dus best om te zoeken naar een middenweg hier. Gelukkig laat GHC voor
\verb|{-# INLINE #-}| pragma's \emph{phase control} toe, wat wil zeggen dat we
meer specifiek kunnen opgeven wanneer GHC moet (of mag) proberen een functie te
inlinen. Om dit te doen, gebruikt GHC een nummering van phases: deze loopt af
naar 0 (de laatste phase). In een \verb|{-# INLINE #-}| pragma kan men
vervolgens dergelijke phases specificeren: Tabel \ref{tabular:inline-pragmas}
geeft een overzicht van de verschillende mogelijkheden.

\begin{table}[h]
\begin{center}
{\renewcommand{\arraystretch}{1.20} % Slightly more spacing
\begin{tabular}{l||cc}
& \textbf{Voor phase |n|} & \textbf{Phase |n| en later} \\
\hline
Geen pragma                    & ?      & ?      \\
\verb|{-# INLINE   f #-}|      & \tick  & \tick  \\
\verb|{-# NOINLINE f #-}|      & \cross & \cross \\
\verb|{-# INLINE   [n]  f #-}| & \cross & \tick  \\
\verb|{-# INLINE   [~n] f #-}| & \tick  & \cross \\
\verb|{-# NOINLINE [n]  f #-}| & \cross & ?      \\
\verb|{-# NOINLINE [~n] f #-}| & ?      & \cross \\
\end{tabular}
}
\end{center}
\caption{Een overzicht van de verschillende \verb|{-# INLINE #-}| pragma's en of
ze de functie |f| wel dan niet inlinen. Bij een ? beslist GHC zelf op basis van
een groot aantal heuristieken.}
\label{tabular:inline-pragmas}
\end{table}

We kiezen dus voor de volgende pragma's voor elke fold en build, zowel voor
lijsten als andere algebra\"ische datatypes:

\begin{lstlisting}
{-# INLINE [0] fold  #-}
{-# INLINE [0] build #-}
\end{lstlisting}

Aangezien phase 0 de laatste phase is, krijgen we zo beide voordelen: voor de
laatste phase worden deze functies nooit ge-inlined, wat foldr/build-fusion
haalbaarder maakt. In de laatste phase worden ze wel ge-inlined, en dus wordt ook
de functiecall-overhead vermeden als er geen mogelijkheid werd gevonden tot
foldr/build-fusion.

Deze pragma's wordt ook automatisch gegenereerd door onze Template Haskell code.
De programmeur hoeft hier dus niet over na te denken.

\section{Detectie van folds}

Een eerste aspect dat we kunnen bekijken is hoe goed de detectie van folds (zie
hoofdstuk \ref{chapter:fold-detection}) werkt. We bespraken reeds dat onze tool
niet alle mogelijk folds kan detecteren. Helaas is het ook zeer intensief werk
om een exacte telling te doen van het aantal folds in codebase, aangezien dit
manueel zou moeten gebeuren. Het lijkt dus niet mogelijk om valse negatieven te
vinden.

We kunnen wel vergelijken met andere tools. Hiervan is \emph{HLint} \cite{hlint}
een voorbeeld. HLint is een tool dat Haskell-packages leest en suggesties geeft
over de gebruikte code-stijl. Het focust dus op refactoring in plaats van
optimalisaties en werkt rechtstreeks op de Haskell-code, waar wij kozen met de
GHC Core te werken (zie sectie \ref{section:ghc-core}). E\'en van de suggesties
die HLint kan geven is het gebruik van |map|, |foldl| of |foldr| in plaats van
expliciete recursie.

We toonden eerder al aan \TODO{backref} dat zowel |map| en |foldl| in termen van
|foldr| uitgredrukt kunnen. Als we dus de som nemen van het aantal functies die
herschreven kunnen worden als |map|, |foldl| of |foldr| volgens HLint, krijgen
we dus het aantal folds over lijsten gedetecteerd door HLint.

We kunnen dit natuurlijk niet rechtstreeks vergelijken met het aantal folds dat
wij detecteren in een Haskell-package: wij detecteren immers folds over alle
algebra\"ische datatypes. We maken dus een onderscheid tussen folds over lijsten
en folds over andere algebra\"ische datatypes.

Een overzicht van de resultaten is te zien in tabel
\ref{tabular:fold-detection-results}. We zien duidelijk dat we meer folds vinden
dan HLint. Bovendien probeerden we onze tool ook uit op de testcases die
meegeleverd worden -- en deze worden allemaal herkent als folds. Dit duidt aan
dat wij een strikte subset van mogelijk folds detecteren.

Het feit dat HLint geen enkele mogelijke fold kan vinden in sommige packages
suggereert ook de auteurs van deze packages misschien HLint gebruiken.

\begin{table}
\begin{center}
{\renewcommand{\arraystretch}{1.20} % Slightly more spacing
\begin{tabular}{l||r||r||r}
\textbf{Package}   & \textbf{List} & \textbf{ADT} & \textbf{HLint} \\
\hline
Cabal-1.16.0.3     & 11            & 9            & 9  \\
containers-0.5.2.1 & 11            & 89           & 1  \\
darcs-2.8.4        & 65            & 1            & 6  \\
ghc-7.6.3          & 216           & 111          & 26 \\
hakyll-4.2.2.0     & 1             & 4            & 0  \\
hlint-1.8.44       & 3             & 3            & 0  \\
hscolour-1.20.3    & 4             & 0            & 2  \\
HTTP-4000.2.8      & 6             & 0            & 3  \\
pandoc-1.11.1      & 15            & 0            & 2  \\
parsec-3.1.3       & 3             & 0            & 0  \\
snap-core-0.9.3.1  & 3             & 1            & 0  \\
\end{tabular}
}
\caption{Een overzicht van het aantal gevonden folds in een aantal bekende
packages.}
\label{tabular:fold-detection-results}
\end{center}
\end{table}

\section{Tijdsmetingen}

We onderzoeken nu de tijdswinsten die we kunnen behalen door foldr/build-fusion
uit te voeren. Hiertoe maken we een lijst kleine programma's die fusable
pijnlijnen van verschillende lengtes bevatten.

We beginnen met een aantal hulpfuncties voor lijsten te defini\"eren op
expliciet recursieve wijze:

\begin{code}
suml :: [Int] -> Int
suml []        = 0
suml (x : xs)  = x + suml xs

mapl :: (a -> b) -> [a] -> [b]
mapl f = go
  where
    go []        = []
    go (x : xs)  = f x : go xs

uptol :: Int -> Int -> [Int]
uptol lo up = go lo
  where
    go i
        | i > up     = []
        | otherwise  = i : uptol (i + 1) up
\end{code}

We kunnen deze hulpfuncties ook defini\"eren voor ons |Tree|-type, opnieuw op
expliciet recursieve wijze:

\begin{code}
sumt :: Tree Int -> Int
sumt (Leaf x)      = x
sumt (Branch l r)  = sumt l + sumt r

mapt :: (a -> b) -> Tree a -> Tree b
mapt f = go
  where
    go (Leaf x)      = Leaf (f x)
    go (Branch l r)  = Branch (go l) (go r)

uptot :: Int -> Int -> Tree Int
uptot lo hi
    | lo >= hi   = Leaf lo
    | otherwise  =
        let mid = (lo + hi) `div` 2
        in Branch (uptot lo mid) (uptot (mid + 1) hi)
\end{code}

Met deze hulpfuncties ter beschikking kunnen we een aantal pijplijnfuncties
maken voor zowel lijsten als bomen, van vari\"erende lengte:

\begin{code}
l1, l2, l3, l4, l5 :: Int -> Int
l1 n = suml (1 `uptol` n)
l2 n = suml (mapl (+ 1) (1 `uptol` n))
l3 n = suml (mapl (+ 1) (mapl (+ 1) (1 `uptol` n)))
l4 n = elapsed
l5 n = elapsed
\end{code}

\begin{code}
t1, t2, t3, t4, t5 :: Int -> Int
t1 n = sumt (1 `uptot` n)
t2 n = sumt (mapt (+ 1) (1 `uptot` n))
t3 n = sumt (mapt (+ 1) (mapt (+ 1) (1 `uptot` n)))
t4 n = elapsed
t5 n = elapsed
\end{code}

Deze functies zijn eenvoudig te benchmarken met behulp van de Criterion
bibliotheek \cite{criterion}. We gebruiken inputgrootte |n = 100000| en voeren
de benchmarks tweemaal uit: enerzijds met enkel de \texttt{-O2} compilatievlag,
en anderzijds met de compilatievlaggen \texttt{-O2 -package what-morphism
-fplugin WhatMorphism}.

De resultaten zijn te zien in Figuur \ref{figure:list-tree} en Figuur
\ref{figure:list-tree-speedups}. We zijn telkens ge\"interesseerd in de
versnelling, die we kunnen berekenen als:

\begin{equation*}
versnelling = \frac{t_2 - t_1}{t_2}
\end{equation*}

Met $t_2$ de tijdsmeting als we compileerden met \emph{what-morphism} en $t_1$
de tijdsmeting met enkel de \texttt{-O2} vlag.

We zien dat we direct grote speedups krijgen bij |l0| en |t0|. Dit toont aan dat
foldr/build-fusion zelfs voor heel kleine pipelines de moeite loont. Eveneens
kunnen we uit de grafiek me relatieve resultaten afleiden dat de versnelling
steeds dichter bij 100\% zal komen naarmate de pijplijn langer wordt.

\begin{figure}[h]
\includegraphics[width=0.50\textwidth]{plots/list.pdf}
\includegraphics[width=0.50\textwidth]{plots/tree.pdf}
\caption{De absolute resultaten van de tijdsmetingen voor lijsten (links) en
bomen (rechts).}
\label{figure:list-tree}

\includegraphics[width=0.50\textwidth]{plots/list-speedups.pdf}
\includegraphics[width=0.50\textwidth]{plots/tree-speedups.pdf}
\caption{De relatieve resultaten van de tijdsmetingen voor lijsten (links) en
bomen (rechts).}
\label{figure:list-tree-speedups}
\end{figure}

\begin{itemize}
\item \TODO{Mutually recursive functions}
\item \TODO{Compilatie ies trager}
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
\bibliographystyle{unsrtnat}
\bibliography{references}

\end{document}
