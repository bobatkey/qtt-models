\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{workingnote}[2018/02/09 Working note class]

\RequirePackage{etoolbox}       % toggles; fixing titlesec.
\newtoggle{ribbons}

\DeclareOption{ribbons}{\toggletrue{ribbons}}
\DeclareOption{noribbons}{\togglefalse{ribbons}}

\ExecuteOptions{}
\ProcessOptions\relax

\LoadClass{article}

\RequirePackage[dvipsnames]{xcolor}
\definecolor[named]{ACMBlue}{cmyk}{1,0.1,0,0.1}
\definecolor[named]{ACMYellow}{cmyk}{0,0.16,1,0}
\definecolor[named]{ACMOrange}{cmyk}{0,0.42,1,0.01}
\definecolor[named]{ACMRed}{cmyk}{0,0.90,0.86,0}
\definecolor[named]{ACMLightBlue}{cmyk}{0.49,0.01,0,0}
\definecolor[named]{ACMGreen}{cmyk}{0.20,0,1,0.19}
\definecolor[named]{ACMPurple}{cmyk}{0.55,1,0,0.15}
\definecolor[named]{ACMDarkBlue}{cmyk}{1,0.58,0,0.21}

% from https://tex.stackexchange.com/questions/269569/widening-marginparwidth-for-verbose-todo-notes
\usepackage[a4paper,
            inner=30mm,
            outer=30mm,% = marginparsep + marginparwidth
                       %   + 5mm (between marginpar and page border)
            top=20mm,
            bottom=25mm,
            marginparsep=5mm,
            marginparwidth=20mm,
            twoside
            %showframe
           ]{geometry}
\usepackage{stmaryrd}
\usepackage{mathpartir}
\usepackage{hyperref}
\usepackage{cmll}
\usepackage{amssymb}
\usepackage[standard,thmmarks]{ntheorem}
\usepackage{mathtools}
\usepackage{libertine}
\usepackage{newtxmath}
\usepackage{zi4}
\usepackage{natbib}
%\usepackage[usenames]{color}
\usepackage{todonotes}


\def\sectionautorefname{Section}
\def\subsectionautorefname{Section}
\def\subsubsectionautorefname{Section}
\definecolor{citationcolour}{rgb}{0,0.4,0.2}
\definecolor{linkcolour}{rgb}{0,0,0.8}

% FIXME: single thread of numbering

% \newtheorem{lemma}{Lemma}
% \newtheorem{proposition}{Proposition}
% \newtheorem{theorem}{Theorem}
% \newtheorem{corollary}{Corollary}
% \newtheorem{conjecture}{Conjecture}
% \theoremstyle{definition}
% \newtheorem{definition}{Definition}
% \newtheorem{example}{Example}

\newcommand{\lemref}[1]{\hyperref[#1]{Lemma \ref*{#1}}}
\newcommand{\exref}[1]{\hyperref[#1]{Example \ref*{#1}}}
\newcommand{\judgeref}[1]{\hyperref[#1]{Judgement \ref*{#1}}}
\newcommand{\propref}[1]{\hyperref[#1]{Proposition \ref*{#1}}}
\newcommand{\diagref}[1]{\hyperref[#1]{Diagram \ref*{#1}}}
\newcommand{\thmref}[1]{\hyperref[#1]{Theorem \ref*{#1}}}
\newcommand{\defref}[1]{\hyperref[#1]{Definition \ref*{#1}}}

\newcommand{\dotsabove}[1]{
  {\begin{array}[b]{c}
    \vdots \\ #1
  \end{array}}}

\newcommand{\authoremail}[1]{\def\@email{#1}}

\hypersetup{colorlinks=true,
  urlcolor=linkcolour,
  linkcolor=linkcolour,
  citecolor=citationcolour}

\AtBeginDocument{%
  \hypersetup{pdftitle=\@title,
    pdfauthor=\@author}}

\renewcommand{\maketitle}{%
  \vspace*{3em}

  \begin{center}
    {\huge \@title}

    \medskip

    {\large \@author} \quad {$\langle$\texttt{\@email}$\rangle$}
  \end{center}

  \vspace{3em}
}

\newcommand{\titlesize}{\Large}
\newcommand{\authorsize}{\normalsize}
\newcommand{\secsize}{\large}
\newcommand{\subsecsize}{\normalsize}
\newcommand{\subsubsecsize}{\normalsize}

% ---------- Section titles from rntz.cls
\RequirePackage{titlesec}

%% titlesec < 2.10.2 has a bug that prevents showing section numbers. This fixes
%% it. Taken from
%% https://tex.stackexchange.com/questions/96090/formatting-subsections-and-chapters-in-tufte-book/96125
\patchcmd{\ttlh@hang}{\parindent\z@}{\parindent\z@\leavevmode}{}{}
\patchcmd{\ttlh@hang}{\noindent}{}{}{}

% Lotsa whitespace.
\titlespacing*{\section}{0pt}{4\parsep}{2\parsep}
\titlespacing*{\subsection}{0pt}{4\parsep}{2\parsep}
\titlespacing*{\subsubsection}{0pt}{4\parsep}{2\parsep}

%% Spacing.
\newcommand{\header}{\rmfamily\bfseries}
%% \renewcommand{\header}{\rmfamily\itshape}  % or, italics
%% \renewcommand{\header}{\sffamily\bfseries} % or, sans-serif

\newcommand{\hnopost}{\hspace*{0mm}}
\newcommand{\hnopre}{\hspace*{2.5mm}}
\newcommand{\makehno}[3]{%
  \llap{\colorbox{#1}{\parbox[t]{100in}{\hfill{\color{#2}#3\hnopost}}}\hnopre}}

\newcommand{\hno}[1]{\makehno{white}{black!50}{#1}}
\iftoggle{ribbons}
   {\newcommand{\colorhno}[3]{\makehno{#1}{#2}{#3}}}
   {\newcommand{\colorhno}[3]{\hno{#3}}}

% Nice colors: Periwinkle, Whee, cyan
\definecolor[named]{Whee}{cmyk}{0.33, 0.33, 0, 0}
\titleformat{\section}{\secsize\header}
            {\colorhno{Whee}{white}{\thesection}}{0pt}{}
\titleformat{\subsection}{\subsecsize\header}{\hno{\thesubsection}}{0pt}{}
% sub-subsections have no heading numbers
\titleformat{\subsubsection}{\subsecsize\header}{\hno{\thesubsubsection}}{0pt}{}
