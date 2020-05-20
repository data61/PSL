(* Title: thys/UTM.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
*)

chapter \<open>Construction of a Universal Turing Machine\<close>

theory UTM
  imports Recursive Abacus UF HOL.GCD Turing_Hoare
begin

section \<open>Wang coding of input arguments\<close>

text \<open>
  The direct compilation of the universal function \<open>rec_F\<close> can
  not give us UTM, because \<open>rec_F\<close> is of arity 2, where the
  first argument represents the Godel coding of the TM being simulated
  and the second argument represents the right number (in Wang's
  coding) of the TM tape.  (Notice, left number is always \<open>0\<close>
  at the very beginning). However, UTM needs to simulate the execution
  of any TM which may very well take many input arguments. Therefore,
  a initialization TM needs to run before the TM compiled from \<open>rec_F\<close>, and the sequential composition of these two TMs will give
  rise to the UTM we are seeking. The purpose of this initialization
  TM is to transform the multiple input arguments of the TM being
  simulated into Wang's coding, so that it can be consumed by the TM
  compiled from \<open>rec_F\<close> as the second argument.

  However, this initialization TM (named \<open>t_wcode\<close>) can not be
  constructed by compiling from any recursive function, because every
  recursive function takes a fixed number of input arguments, while
  \<open>t_wcode\<close> needs to take varying number of arguments and
  tranform them into Wang's coding. Therefore, this section give a
  direct construction of \<open>t_wcode\<close> with just some parts being
  obtained from recursive functions.

\newlength{\basewidth}
\settowidth{\basewidth}{xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx}
\newlength{\baseheight}
\settoheight{\baseheight}{$B:R$}
\newcommand{\vsep}{5\baseheight}

The TM used to generate the Wang's code of input arguments is divided into three TMs
 executed sequentially, namely $prepare$, $mainwork$ and $adjust$.
 According to the
 convention, the start state of ever TM is fixed to state $1$ while the final state is
 fixed to $0$.

The input and output of $prepare$ are illustrated respectively by Figure
\ref{prepare_input} and \ref{prepare_output}.


\begin{figure}[h!]
\centering
\scalebox{1.2}{
\begin{tikzpicture}
  [tbox/.style = {draw, thick, inner sep = 5pt}]
  \node (0) {};
  \node (1) [tbox, text height = 3.5pt, right = -0.9pt of 0] {$m$};
  \node (2) [tbox, right = -0.9pt of 1] {$0$};
  \node (3) [tbox, right = -0.9pt of 2] {$a_1$};
  \node (4) [tbox, right = -0.9pt of 3] {$0$};
  \node (5) [tbox, right = -0.9pt of 4] {$a_2$};
  \node (6) [right = -0.9pt of 5] {\ldots \ldots};
  \node (7) [tbox, right = -0.9pt of 6] {$a_n$};
  \draw [->, >=latex, thick] (1)+(0, -4\baseheight) -- (1);
\end{tikzpicture}}
\caption{The input of TM $prepare$} \label{prepare_input}
\end{figure}

\begin{figure}[h!]
\centering
\scalebox{1.2}{
\begin{tikzpicture}
  \node (0) {};
  \node (1) [draw, text height = 3.5pt, right = -0.9pt of 0, thick, inner sep = 5pt] {$m$};
  \node (2) [draw, right = -0.9pt of 1, thick, inner sep = 5pt] {$0$};
  \node (3) [draw, right = -0.9pt of 2, thick, inner sep = 5pt] {$0$};
  \node (4) [draw, right = -0.9pt of 3, thick, inner sep = 5pt] {$a_1$};
  \node (5) [draw, right = -0.9pt of 4, thick, inner sep = 5pt] {$0$};
  \node (6) [draw, right = -0.9pt of 5, thick, inner sep = 5pt] {$a_2$};
  \node (7) [right = -0.9pt of 6] {\ldots \ldots};
  \node (8) [draw, right = -0.9pt of 7, thick, inner sep = 5pt] {$a_n$};
  \node (9) [draw, right = -0.9pt of 8, thick, inner sep = 5pt] {$0$};
  \node (10) [draw, right = -0.9pt of 9, thick, inner sep = 5pt] {$0$};
  \node (11) [draw, right = -0.9pt of 10, thick, inner sep = 5pt] {$1$};
  \draw [->, >=latex, thick] (10)+(0, -4\baseheight) -- (10);
\end{tikzpicture}}
\caption{The output of TM $prepare$} \label{prepare_output}
\end{figure}

As shown in Figure \ref{prepare_input}, the input of $prepare$ is the
same as the the input of UTM, where $m$ is the Godel coding of the TM
being interpreted and $a_1$ through $a_n$ are the $n$ input arguments
of the TM under interpretation. The purpose of $purpose$ is to
transform this initial tape layout to the one shown in Figure
\ref{prepare_output}, which is convenient for the generation of Wang's
codding of $a_1, \ldots, a_n$. The coding procedure starts from $a_n$
and ends after $a_1$ is encoded. The coding result is stored in an
accumulator at the end of the tape (initially represented by the $1$
two blanks right to $a_n$ in Figure \ref{prepare_output}). In Figure
\ref{prepare_output}, arguments $a_1, \ldots, a_n$ are separated by
two blanks on both ends with the rest so that movement conditions can
be implemented conveniently in subsequent TMs, because, by convention,
two consecutive blanks are usually used to signal the end or start of
a large chunk of data. The diagram of $prepare$ is given in Figure
\ref{prepare_diag}.


\begin{figure}[h!]
\centering
\scalebox{0.9}{
\begin{tikzpicture}
     \node[circle,draw] (1) {$1$};
     \node[circle,draw] (2) at ($(1)+(0.3\basewidth, 0)$) {$2$};
     \node[circle,draw] (3) at ($(2)+(0.3\basewidth, 0)$) {$3$};
     \node[circle,draw] (4) at ($(3)+(0.3\basewidth, 0)$) {$4$};
     \node[circle,draw] (5) at ($(4)+(0.3\basewidth, 0)$) {$5$};
     \node[circle,draw] (6) at ($(5)+(0.3\basewidth, 0)$) {$6$};
     \node[circle,draw] (7) at ($(6)+(0.3\basewidth, 0)$) {$7$};
     \node[circle,draw] (8) at ($(7)+(0.3\basewidth, 0)$) {$0$};


     \draw [->, >=latex] (1) edge [loop above] node[above] {$S_1:L$} (1)
     ;
     \draw [->, >=latex] (1) -- node[above] {$S_0:S_1$} (2)
     ;
     \draw [->, >=latex] (2) edge [loop above] node[above] {$S_1:R$} (2)
     ;
     \draw [->, >=latex] (2) -- node[above] {$S_0:L$} (3)
     ;
     \draw [->, >=latex] (3) edge[loop above] node[above] {$S_1:S_0$} (3)
     ;
     \draw [->, >=latex] (3) -- node[above] {$S_0:R$} (4)
     ;
     \draw [->, >=latex] (4) edge[loop above] node[above] {$S_0:R$} (4)
     ;
     \draw [->, >=latex] (4) -- node[above] {$S_0:R$} (5)
     ;
     \draw [->, >=latex] (5) edge[loop above] node[above] {$S_1:R$} (5)
     ;
     \draw [->, >=latex] (5) -- node[above] {$S_0:R$} (6)
     ;
     \draw [->, >=latex] (6) edge[bend left = 50] node[below] {$S_1:R$} (5)
     ;
     \draw [->, >=latex] (6) -- node[above] {$S_0:R$} (7)
     ;
     \draw [->, >=latex] (7) edge[loop above] node[above] {$S_0:S_1$} (7)
     ;
     \draw [->, >=latex] (7) -- node[above] {$S_1:L$} (8)
     ;
 \end{tikzpicture}}
\caption{The diagram of TM $prepare$} \label{prepare_diag}
\end{figure}

The purpose of TM $mainwork$ is to compute the Wang's encoding of $a_1, \ldots, a_n$. Every bit of $a_1, \ldots, a_n$, including the separating bits, is processed from left to right.
In order to detect the termination condition when the left most bit of $a_1$ is reached,
TM $mainwork$ needs to look ahead and consider three different situations at the start of
every iteration:
\begin{enumerate}
    \item The TM configuration for the first situation is shown in Figure \ref{mainwork_case_one_input},
        where the accumulator is stored in $r$, both of the next two bits
        to be encoded are $1$. The configuration at the end of the iteration
        is shown in Figure \ref{mainwork_case_one_output}, where the first 1-bit has been
        encoded and cleared. Notice that the accumulator has been changed to
        $(r+1) \times 2$ to reflect the encoded bit.
    \item The TM configuration for the second situation is shown in Figure
        \ref{mainwork_case_two_input},
        where the accumulator is stored in $r$, the next two bits
        to be encoded are $1$ and $0$. After the first
        $1$-bit was encoded and cleared, the second $0$-bit is difficult to detect
        and process. To solve this problem, these two consecutive bits are
        encoded in one iteration.  In this situation, only the first $1$-bit needs
        to be cleared since the second one is cleared by definition.
        The configuration at the end of the iteration
        is shown in Figure \ref{mainwork_case_two_output}.
        Notice that the accumulator has been changed to
        $(r+1) \times 4$ to reflect the two encoded bits.
    \item The third situation corresponds to the case when the last bit of $a_1$ is reached.
        The TM configurations at the start and end of the iteration are shown in
        Figure \ref{mainwork_case_three_input} and \ref{mainwork_case_three_output}
        respectively. For this situation, only the read write head needs to be moved to
        the left to prepare a initial configuration for TM $adjust$ to start with.
\end{enumerate}
The diagram of $mainwork$ is given in Figure \ref{mainwork_diag}. The two rectangular nodes
labeled with $2 \times x$ and $4 \times x$ are two TMs compiling from recursive functions
so that we do not have to design and verify two quite complicated TMs.


\begin{figure}[h!]
\centering
\scalebox{1.2}{
\begin{tikzpicture}
  \node (0) {};
  \node (1) [draw, text height = 3.9pt, right = -0.9pt of 0, thick, inner sep = 5pt] {$m$};
  \node (2) [draw, right = -0.9pt of 1, thick, inner sep = 5pt] {$0$};
  \node (3) [draw, right = -0.9pt of 2, thick, inner sep = 5pt] {$0$};
  \node (4) [draw, right = -0.9pt of 3, thick, inner sep = 5pt] {$a_1$};
  \node (5) [draw, right = -0.9pt of 4, thick, inner sep = 5pt] {$0$};
  \node (6) [draw, right = -0.9pt of 5, thick, inner sep = 5pt] {$a_2$};
  \node (7) [right = -0.9pt of 6] {\ldots \ldots};
  \node (8) [draw, right = -0.9pt of 7, thick, inner sep = 5pt] {$a_i$};
  \node (9) [draw, right = -0.9pt of 8, thick, inner sep = 5pt] {$1$};
  \node (10) [draw, right = -0.9pt of 9, thick, inner sep = 5pt] {$1$};
  \node (11) [draw, right = -0.9pt of 10, thick, inner sep = 5pt] {$0$};
  \node (12) [right = -0.9pt of 11] {\ldots \ldots};
  \node (13) [draw, right = -0.9pt of 12, thick, inner sep = 5pt] {$0$};
  \node (14) [draw, text height = 3.9pt, right = -0.9pt of 13, thick, inner sep = 5pt] {$r$};
  \draw [->, >=latex, thick] (13)+(0, -4\baseheight) -- (13);
\end{tikzpicture}}
\caption{The first situation for TM $mainwork$ to consider} \label{mainwork_case_one_input}
\end{figure}


\begin{figure}[h!]
\centering
\scalebox{1.2}{
\begin{tikzpicture}
  \node (0) {};
  \node (1) [draw, text height = 3.9pt, right = -0.9pt of 0, thick, inner sep = 5pt] {$m$};
  \node (2) [draw, right = -0.9pt of 1, thick, inner sep = 5pt] {$0$};
  \node (3) [draw, right = -0.9pt of 2, thick, inner sep = 5pt] {$0$};
  \node (4) [draw, right = -0.9pt of 3, thick, inner sep = 5pt] {$a_1$};
  \node (5) [draw, right = -0.9pt of 4, thick, inner sep = 5pt] {$0$};
  \node (6) [draw, right = -0.9pt of 5, thick, inner sep = 5pt] {$a_2$};
  \node (7) [right = -0.9pt of 6] {\ldots \ldots};
  \node (8) [draw, right = -0.9pt of 7, thick, inner sep = 5pt] {$a_i$};
  \node (9) [draw, right = -0.9pt of 8, thick, inner sep = 5pt] {$1$};
  \node (10) [draw, right = -0.9pt of 9, thick, inner sep = 5pt] {$0$};
  \node (11) [draw, right = -0.9pt of 10, thick, inner sep = 5pt] {$0$};
  \node (12) [right = -0.9pt of 11] {\ldots \ldots};
  \node (13) [draw, right = -0.9pt of 12, thick, inner sep = 5pt] {$0$};
  \node (14) [draw, text height = 2.7pt, right = -0.9pt of 13, thick, inner sep = 5pt] {$(r+1) \times 2$};
  \draw [->, >=latex, thick] (13)+(0, -4\baseheight) -- (13);
\end{tikzpicture}}
\caption{The output for the first case of TM $mainwork$'s processing}
\label{mainwork_case_one_output}
\end{figure}

\begin{figure}[h!]
\centering
\scalebox{1.2}{
\begin{tikzpicture}
  \node (0) {};
  \node (1) [draw, text height = 3.9pt, right = -0.9pt of 0, thick, inner sep = 5pt] {$m$};
  \node (2) [draw, right = -0.9pt of 1, thick, inner sep = 5pt] {$0$};
  \node (3) [draw, right = -0.9pt of 2, thick, inner sep = 5pt] {$0$};
  \node (4) [draw, right = -0.9pt of 3, thick, inner sep = 5pt] {$a_1$};
  \node (5) [draw, right = -0.9pt of 4, thick, inner sep = 5pt] {$0$};
  \node (6) [draw, right = -0.9pt of 5, thick, inner sep = 5pt] {$a_2$};
  \node (7) [right = -0.9pt of 6] {\ldots \ldots};
  \node (8) [draw, right = -0.9pt of 7, thick, inner sep = 5pt] {$a_i$};
  \node (9) [draw, right = -0.9pt of 8, thick, inner sep = 5pt] {$1$};
  \node (10) [draw, right = -0.9pt of 9, thick, inner sep = 5pt] {$0$};
  \node (11) [draw, right = -0.9pt of 10, thick, inner sep = 5pt] {$1$};
  \node (12) [draw, right = -0.9pt of 11, thick, inner sep = 5pt] {$0$};
  \node (13) [right = -0.9pt of 12] {\ldots \ldots};
  \node (14) [draw, right = -0.9pt of 13, thick, inner sep = 5pt] {$0$};
  \node (15) [draw, text height = 3.9pt, right = -0.9pt of 14, thick, inner sep = 5pt] {$r$};
  \draw [->, >=latex, thick] (14)+(0, -4\baseheight) -- (14);
\end{tikzpicture}}
\caption{The second situation for TM $mainwork$ to consider} \label{mainwork_case_two_input}
\end{figure}

\begin{figure}[h!]
\centering
\scalebox{1.2}{
\begin{tikzpicture}
  \node (0) {};
  \node (1) [draw, text height = 3.9pt, right = -0.9pt of 0, thick, inner sep = 5pt] {$m$};
  \node (2) [draw, right = -0.9pt of 1, thick, inner sep = 5pt] {$0$};
  \node (3) [draw, right = -0.9pt of 2, thick, inner sep = 5pt] {$0$};
  \node (4) [draw, right = -0.9pt of 3, thick, inner sep = 5pt] {$a_1$};
  \node (5) [draw, right = -0.9pt of 4, thick, inner sep = 5pt] {$0$};
  \node (6) [draw, right = -0.9pt of 5, thick, inner sep = 5pt] {$a_2$};
  \node (7) [right = -0.9pt of 6] {\ldots \ldots};
  \node (8) [draw, right = -0.9pt of 7, thick, inner sep = 5pt] {$a_i$};
  \node (9) [draw, right = -0.9pt of 8, thick, inner sep = 5pt] {$1$};
  \node (10) [draw, right = -0.9pt of 9, thick, inner sep = 5pt] {$0$};
  \node (11) [draw, right = -0.9pt of 10, thick, inner sep = 5pt] {$0$};
  \node (12) [draw, right = -0.9pt of 11, thick, inner sep = 5pt] {$0$};
  \node (13) [right = -0.9pt of 12] {\ldots \ldots};
  \node (14) [draw, right = -0.9pt of 13, thick, inner sep = 5pt] {$0$};
  \node (15) [draw, text height = 2.7pt, right = -0.9pt of 14, thick, inner sep = 5pt] {$(r+1) \times 4$};
  \draw [->, >=latex, thick] (14)+(0, -4\baseheight) -- (14);
\end{tikzpicture}}
\caption{The output for the second case of TM $mainwork$'s processing}
\label{mainwork_case_two_output}
\end{figure}

\begin{figure}[h!]
\centering
\scalebox{1.2}{
\begin{tikzpicture}
  \node (0) {};
  \node (1) [draw, text height = 3.9pt, right = -0.9pt of 0, thick, inner sep = 5pt] {$m$};
  \node (2) [draw, right = -0.9pt of 1, thick, inner sep = 5pt] {$0$};
  \node (3) [draw, right = -0.9pt of 2, thick, inner sep = 5pt] {$0$};
  \node (4) [draw, right = -0.9pt of 3, thick, inner sep = 5pt] {$1$};
  \node (5) [draw, right = -0.9pt of 4, thick, inner sep = 5pt] {$0$};
  \node (6) [right = -0.9pt of 5] {\ldots \ldots};
  \node (7) [draw, right = -0.9pt of 6, thick, inner sep = 5pt] {$0$};
  \node (8) [draw, text height = 3.9pt, right = -0.9pt of 7, thick, inner sep = 5pt] {$r$};
  \draw [->, >=latex, thick] (7)+(0, -4\baseheight) -- (7);
\end{tikzpicture}}
\caption{The third situation for TM $mainwork$ to consider} \label{mainwork_case_three_input}
\end{figure}

\begin{figure}[h!]
\centering
\scalebox{1.2}{
\begin{tikzpicture}
  \node (0) {};
  \node (1) [draw, text height = 3.9pt, right = -0.9pt of 0, thick, inner sep = 5pt] {$m$};
  \node (2) [draw, right = -0.9pt of 1, thick, inner sep = 5pt] {$0$};
  \node (3) [draw, right = -0.9pt of 2, thick, inner sep = 5pt] {$0$};
  \node (4) [draw, right = -0.9pt of 3, thick, inner sep = 5pt] {$1$};
  \node (5) [draw, right = -0.9pt of 4, thick, inner sep = 5pt] {$0$};
  \node (6) [right = -0.9pt of 5] {\ldots \ldots};
  \node (7) [draw, right = -0.9pt of 6, thick, inner sep = 5pt] {$0$};
  \node (8) [draw, text height = 3.9pt, right = -0.9pt of 7, thick, inner sep = 5pt] {$r$};
  \draw [->, >=latex, thick] (3)+(0, -4\baseheight) -- (3);
\end{tikzpicture}}
\caption{The output for the third case of TM $mainwork$'s processing}
\label{mainwork_case_three_output}
\end{figure}

\begin{figure}[h!]
\centering
\scalebox{0.9}{
\begin{tikzpicture}
     \node[circle,draw] (1) {$1$};
     \node[circle,draw] (2) at ($(1)+(0.3\basewidth, 0)$) {$2$};
     \node[circle,draw] (3) at ($(2)+(0.3\basewidth, 0)$) {$3$};
     \node[circle,draw] (4) at ($(3)+(0.3\basewidth, 0)$) {$4$};
     \node[circle,draw] (5) at ($(4)+(0.3\basewidth, 0)$) {$5$};
     \node[circle,draw] (6) at ($(5)+(0.3\basewidth, 0)$) {$6$};
     \node[circle,draw] (7) at ($(2)+(0, -7\baseheight)$) {$7$};
     \node[circle,draw] (8) at ($(7)+(0, -7\baseheight)$) {$8$};
     \node[circle,draw] (9) at ($(8)+(0.3\basewidth, 0)$) {$9$};
     \node[circle,draw] (10) at ($(9)+(0.3\basewidth, 0)$) {$10$};
     \node[circle,draw] (11) at ($(10)+(0.3\basewidth, 0)$) {$11$};
     \node[circle,draw] (12) at ($(11)+(0.3\basewidth, 0)$) {$12$};
     \node[draw] (13) at ($(6)+(0.3\basewidth, 0)$) {$2 \times x$};
     \node[circle,draw] (14) at ($(13)+(0.3\basewidth, 0)$) {$j_1$};
     \node[draw] (15) at ($(12)+(0.3\basewidth, 0)$) {$4 \times x$};
     \node[draw] (16) at ($(15)+(0.3\basewidth, 0)$) {$j_2$};
     \node[draw] (17) at ($(7)+(0.3\basewidth, 0)$) {$0$};

     \draw [->, >=latex] (1) edge[loop left] node[above] {$S_0:L$} (1)
     ;
     \draw [->, >=latex] (1) -- node[above] {$S_1:L$} (2)
     ;
     \draw [->, >=latex] (2) -- node[above] {$S_1:R$} (3)
     ;
     \draw [->, >=latex] (2) -- node[left] {$S_1:L$} (7)
     ;
     \draw [->, >=latex] (3) edge[loop above] node[above] {$S_1:S_0$} (3)
     ;
     \draw [->, >=latex] (3) -- node[above] {$S_0:R$} (4)
     ;
     \draw [->, >=latex] (4) edge[loop above] node[above] {$S_0:R$} (4)
     ;
     \draw [->, >=latex] (4) -- node[above] {$S_1:R$} (5)
     ;
     \draw [->, >=latex] (5) edge[loop above] node[above] {$S_1:R$} (5)
     ;
     \draw [->, >=latex] (5) -- node[above] {$S_0:S_1$} (6)
     ;
     \draw [->, >=latex] (6) edge[loop above] node[above] {$S_1:L$} (6)
     ;
     \draw [->, >=latex] (6) -- node[above] {$S_0:R$} (13)
     ;
     \draw [->, >=latex] (13) -- (14)
     ;
     \draw (14) -- ($(14)+(0, 6\baseheight)$) -- ($(1) + (0, 6\baseheight)$) node [above,midway] {$S_1:L$}
     ;
     \draw [->, >=latex] ($(1) + (0, 6\baseheight)$) -- (1)
     ;
     \draw [->, >=latex] (7) -- node[above] {$S_0:R$} (17)
     ;
     \draw [->, >=latex] (7) -- node[left] {$S_1:R$} (8)
     ;
     \draw [->, >=latex] (8) -- node[above] {$S_0:R$} (9)
     ;
     \draw [->, >=latex] (9) -- node[above] {$S_0:R$} (10)
     ;
     \draw [->, >=latex] (10) -- node[above] {$S_1:R$} (11)
     ;
     \draw [->, >=latex] (10) edge[loop above] node[above] {$S_0:R$} (10)
     ;
     \draw [->, >=latex] (11) edge[loop above] node[above] {$S_1:R$} (11)
     ;
     \draw [->, >=latex] (11) -- node[above] {$S_0:S_1$} (12)
     ;
     \draw [->, >=latex] (12) -- node[above] {$S_0:R$} (15)
     ;
     \draw [->, >=latex] (12) edge[loop above] node[above] {$S_1:L$} (12)
     ;
     \draw [->, >=latex] (15) -- (16)
     ;
     \draw (16) -- ($(16)+(0, -4\baseheight)$) -- ($(1) + (0, -18\baseheight)$) node [below,midway] {$S_1:L$}
     ;
     \draw [->, >=latex] ($(1) + (0, -18\baseheight)$) -- (1)
     ;
 \end{tikzpicture}}
\caption{The diagram of TM $mainwork$} \label{mainwork_diag}
\end{figure}

The purpose of TM $adjust$ is to encode the last bit of $a_1$. The initial and final configuration
of this TM are shown in Figure \ref{adjust_initial} and \ref{adjust_final} respectively.
The diagram of TM $adjust$ is shown in Figure \ref{adjust_diag}.


\begin{figure}[h!]
\centering
\scalebox{1.2}{
\begin{tikzpicture}
  \node (0) {};
  \node (1) [draw, text height = 3.9pt, right = -0.9pt of 0, thick, inner sep = 5pt] {$m$};
  \node (2) [draw, right = -0.9pt of 1, thick, inner sep = 5pt] {$0$};
  \node (3) [draw, right = -0.9pt of 2, thick, inner sep = 5pt] {$0$};
  \node (4) [draw, right = -0.9pt of 3, thick, inner sep = 5pt] {$1$};
  \node (5) [draw, right = -0.9pt of 4, thick, inner sep = 5pt] {$0$};
  \node (6) [right = -0.9pt of 5] {\ldots \ldots};
  \node (7) [draw, right = -0.9pt of 6, thick, inner sep = 5pt] {$0$};
  \node (8) [draw, text height = 3.9pt, right = -0.9pt of 7, thick, inner sep = 5pt] {$r$};
  \draw [->, >=latex, thick] (3)+(0, -4\baseheight) -- (3);
\end{tikzpicture}}
\caption{Initial configuration of TM $adjust$} \label{adjust_initial}
\end{figure}

\begin{figure}[h!]
\centering
\scalebox{1.2}{
\begin{tikzpicture}
  \node (0) {};
  \node (1) [draw, text height = 3.9pt, right = -0.9pt of 0, thick, inner sep = 5pt] {$m$};
  \node (2) [draw, right = -0.9pt of 1, thick, inner sep = 5pt] {$0$};
  \node (3) [draw, text height = 2.9pt, right = -0.9pt of 2, thick, inner sep = 5pt] {$r+1$};
  \node (4) [draw, right = -0.9pt of 3, thick, inner sep = 5pt] {$0$};
  \node (5) [draw, right = -0.9pt of 4, thick, inner sep = 5pt] {$0$};
  \node (6) [right = -0.9pt of 5] {\ldots \ldots};
  \draw [->, >=latex, thick] (1)+(0, -4\baseheight) -- (1);
\end{tikzpicture}}
\caption{Final configuration of TM $adjust$} \label{adjust_final}
\end{figure}


\begin{figure}[h!]
\centering
\scalebox{0.9}{
\begin{tikzpicture}
     \node[circle,draw] (1) {$1$};
     \node[circle,draw] (2) at ($(1)+(0.3\basewidth, 0)$) {$2$};
     \node[circle,draw] (3) at ($(2)+(0.3\basewidth, 0)$) {$3$};
     \node[circle,draw] (4) at ($(3)+(0.3\basewidth, 0)$) {$4$};
     \node[circle,draw] (5) at ($(4)+(0.3\basewidth, 0)$) {$5$};
     \node[circle,draw] (6) at ($(5)+(0.3\basewidth, 0)$) {$6$};
     \node[circle,draw] (7) at ($(6)+(0.3\basewidth, 0)$) {$7$};
     \node[circle,draw] (8) at ($(4)+(0, -7\baseheight)$) {$8$};
     \node[circle,draw] (9) at ($(8)+(0.3\basewidth, 0)$) {$9$};
     \node[circle,draw] (10) at ($(9)+(0.3\basewidth, 0)$) {$10$};
     \node[circle,draw] (11) at ($(10)+(0.3\basewidth, 0)$) {$11$};
     \node[circle,draw] (12) at ($(11)+(0.3\basewidth, 0)$) {$0$};


     \draw [->, >=latex] (1) -- node[above] {$S_1:R$} (2)
     ;
     \draw [->, >=latex] (1) edge[loop above] node[above] {$S_0:S_1$} (1)
     ;
     \draw [->, >=latex] (2) -- node[above] {$S_1:R$} (3)
     ;
     \draw [->, >=latex] (3) edge[loop above] node[above] {$S_0:R$} (3)
     ;
     \draw [->, >=latex] (3) -- node[above] {$S_1:R$} (4)
     ;
     \draw [->, >=latex] (4) -- node[above] {$S_1:L$} (5)
     ;
     \draw [->, >=latex] (4) -- node[right] {$S_0:L$} (8)
     ;
     \draw [->, >=latex] (5) -- node[above] {$S_0:L$} (6)
     ;
     \draw [->, >=latex] (5) edge[loop above] node[above] {$S_1:S_0$} (5)
     ;
     \draw [->, >=latex] (6) -- node[above] {$S_1:R$} (7)
     ;
     \draw [->, >=latex] (6) edge[loop above] node[above] {$S_0:L$} (6)
     ;
     \draw (7) -- ($(7)+(0, 6\baseheight)$) -- ($(2) + (0, 6\baseheight)$) node [above,midway] {$S_0:S_1$}
     ;
     \draw [->, >=latex] ($(2) + (0, 6\baseheight)$) -- (2)
     ;
     \draw [->, >=latex] (8) edge[loop left] node[left] {$S_1:S_0$} (8)
     ;
     \draw [->, >=latex] (8) -- node[above] {$S_0:L$} (9)
     ;
     \draw [->, >=latex] (9) edge[loop above] node[above] {$S_0:L$} (9)
     ;
     \draw [->, >=latex] (9) -- node[above] {$S_1:L$} (10)
     ;
     \draw [->, >=latex] (10) edge[loop above] node[above] {$S_0:L$} (10)
     ;
     \draw [->, >=latex] (10) -- node[above] {$S_0:L$} (11)
     ;
     \draw [->, >=latex] (11) edge[loop above] node[above] {$S_1:L$} (11)
     ;
     \draw [->, >=latex] (11) -- node[above] {$S_0:R$} (12)
     ;
 \end{tikzpicture}}
\caption{Diagram of TM $adjust$} \label{adjust_diag}
\end{figure}
\<close>


definition rec_twice :: "recf"
  where
    "rec_twice = Cn 1 rec_mult [id 1 0, constn 2]"

definition rec_fourtimes  :: "recf"
  where
    "rec_fourtimes = Cn 1 rec_mult [id 1 0, constn 4]"

definition abc_twice :: "abc_prog"
  where
    "abc_twice = (let (aprog, ary, fp) = rec_ci rec_twice in 
                       aprog [+] dummy_abc ((Suc 0)))"

definition abc_fourtimes :: "abc_prog"
  where
    "abc_fourtimes = (let (aprog, ary, fp) = rec_ci rec_fourtimes in 
                       aprog [+] dummy_abc ((Suc 0)))"

definition twice_ly :: "nat list"
  where
    "twice_ly = layout_of abc_twice"

definition fourtimes_ly :: "nat list"
  where
    "fourtimes_ly = layout_of abc_fourtimes"

definition t_twice_compile :: "instr list"
  where
    "t_twice_compile= (tm_of abc_twice @ (shift (mopup 1) (length (tm_of abc_twice) div 2)))"

definition t_twice :: "instr list"
  where
    "t_twice = adjust0 t_twice_compile"

definition t_fourtimes_compile :: "instr list"
  where
    "t_fourtimes_compile= (tm_of abc_fourtimes @ (shift (mopup 1) (length (tm_of abc_fourtimes) div 2)))"

definition t_fourtimes :: "instr list"
  where
    "t_fourtimes = adjust0 t_fourtimes_compile"

definition t_twice_len :: "nat"
  where
    "t_twice_len = length t_twice div 2"

definition t_wcode_main_first_part:: "instr list"
  where
    "t_wcode_main_first_part \<equiv> 
                   [(L, 1), (L, 2), (L, 7), (R, 3),
                    (R, 4), (W0, 3), (R, 4), (R, 5),
                    (W1, 6), (R, 5), (R, 13), (L, 6),
                    (R, 0), (R, 8), (R, 9), (Nop, 8),
                    (R, 10), (W0, 9), (R, 10), (R, 11), 
                    (W1, 12), (R, 11), (R, t_twice_len + 14), (L, 12)]"

definition t_wcode_main :: "instr list"
  where
    "t_wcode_main = (t_wcode_main_first_part @ shift t_twice 12 @ [(L, 1), (L, 1)]
                    @ shift t_fourtimes (t_twice_len + 13) @ [(L, 1), (L, 1)])"

fun bl_bin :: "cell list \<Rightarrow> nat"
  where
    "bl_bin [] = 0" 
  | "bl_bin (Bk # xs) = 2 * bl_bin xs"
  | "bl_bin (Oc # xs) = Suc (2 * bl_bin xs)"

declare bl_bin.simps[simp del]

type_synonym bin_inv_t = "cell list \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"

fun wcode_before_double :: "bin_inv_t"
  where
    "wcode_before_double ires rs (l, r) =
     (\<exists> ln rn. l = Bk # Bk # Bk\<up>(ln) @ Oc # ires \<and> 
               r = Oc\<up>((Suc (Suc rs))) @ Bk\<up>(rn ))"

declare wcode_before_double.simps[simp del]

fun wcode_after_double :: "bin_inv_t"
  where
    "wcode_after_double ires rs (l, r) = 
     (\<exists> ln rn. l = Bk # Bk # Bk\<up>(ln) @ Oc # ires \<and>
         r = Oc\<up>(Suc (Suc (Suc 2*rs))) @ Bk\<up>(rn))"

declare wcode_after_double.simps[simp del]

fun wcode_on_left_moving_1_B :: "bin_inv_t"
  where
    "wcode_on_left_moving_1_B ires rs (l, r) = 
     (\<exists> ml mr rn. l = Bk\<up>(ml) @ Oc # Oc # ires \<and> 
               r = Bk\<up>(mr) @ Oc\<up>(Suc rs) @ Bk\<up>(rn) \<and>
               ml + mr > Suc 0 \<and> mr > 0)"

declare wcode_on_left_moving_1_B.simps[simp del]

fun wcode_on_left_moving_1_O :: "bin_inv_t"
  where
    "wcode_on_left_moving_1_O ires rs (l, r) = 
     (\<exists> ln rn.
               l = Oc # ires \<and> 
               r = Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

declare wcode_on_left_moving_1_O.simps[simp del]

fun wcode_on_left_moving_1 :: "bin_inv_t"
  where
    "wcode_on_left_moving_1 ires rs (l, r) = 
          (wcode_on_left_moving_1_B ires rs (l, r) \<or> wcode_on_left_moving_1_O ires rs (l, r))"

declare wcode_on_left_moving_1.simps[simp del]

fun wcode_on_checking_1 :: "bin_inv_t"
  where
    "wcode_on_checking_1 ires rs (l, r) = 
    (\<exists> ln rn. l = ires \<and>
              r = Oc # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

fun wcode_erase1 :: "bin_inv_t"
  where
    "wcode_erase1 ires rs (l, r) = 
       (\<exists> ln rn. l = Oc # ires \<and> 
                 tl r = Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

declare wcode_erase1.simps [simp del]

fun wcode_on_right_moving_1 :: "bin_inv_t"
  where
    "wcode_on_right_moving_1 ires rs (l, r) = 
       (\<exists> ml mr rn.        
             l = Bk\<up>(ml) @ Oc # ires \<and> 
             r = Bk\<up>(mr) @ Oc\<up>(Suc rs) @ Bk\<up>(rn) \<and>
             ml + mr > Suc 0)"

declare wcode_on_right_moving_1.simps [simp del] 

declare wcode_on_right_moving_1.simps[simp del]

fun wcode_goon_right_moving_1 :: "bin_inv_t"
  where
    "wcode_goon_right_moving_1 ires rs (l, r) = 
      (\<exists> ml mr ln rn. 
            l = Oc\<up>(ml) @ Bk # Bk # Bk\<up>(ln) @ Oc # ires \<and> 
            r = Oc\<up>(mr) @ Bk\<up>(rn) \<and>
            ml + mr = Suc rs)"

declare wcode_goon_right_moving_1.simps[simp del]

fun wcode_backto_standard_pos_B :: "bin_inv_t"
  where
    "wcode_backto_standard_pos_B ires rs (l, r) = 
          (\<exists> ln rn. l =  Bk # Bk\<up>(ln) @ Oc # ires \<and> 
               r =  Bk # Oc\<up>((Suc (Suc rs))) @ Bk\<up>(rn ))"

declare wcode_backto_standard_pos_B.simps[simp del]

fun wcode_backto_standard_pos_O :: "bin_inv_t"
  where
    "wcode_backto_standard_pos_O ires rs (l, r) = 
        (\<exists> ml mr ln rn. 
            l = Oc\<up>(ml) @ Bk # Bk # Bk\<up>(ln) @ Oc # ires \<and>
            r = Oc\<up>(mr) @ Bk\<up>(rn) \<and>
            ml + mr = Suc (Suc rs) \<and> mr > 0)"

declare wcode_backto_standard_pos_O.simps[simp del]

fun wcode_backto_standard_pos :: "bin_inv_t"
  where
    "wcode_backto_standard_pos ires rs (l, r) = (wcode_backto_standard_pos_B ires rs (l, r) \<or>
                                            wcode_backto_standard_pos_O ires rs (l, r))"

declare wcode_backto_standard_pos.simps[simp del]

lemma bin_wc_eq: "bl_bin xs = bl2wc xs"
proof(induct xs)
  show " bl_bin [] = bl2wc []" 
    apply(simp add: bl_bin.simps)
    done
next
  fix a xs
  assume "bl_bin xs = bl2wc xs"
  thus " bl_bin (a # xs) = bl2wc (a # xs)"
    apply(case_tac a, simp_all add: bl_bin.simps bl2wc.simps)
     apply(simp_all add: bl2nat.simps bl2nat_double)
    done
qed

lemma tape_of_nl_append_one: "lm \<noteq> [] \<Longrightarrow>  <lm @ [a]> = <lm> @ Bk # Oc\<up>Suc a"
  apply(induct lm, auto simp: tape_of_nl_cons split:if_splits)
  done

lemma tape_of_nl_rev: "rev (<lm::nat list>) = (<rev lm>)"
  apply(induct lm, simp, auto)
  apply(auto simp: tape_of_nl_cons tape_of_nl_append_one split: if_splits)
  apply(simp add: exp_ind[THEN sym])
  done

lemma exp_1[simp]: "a\<up>(Suc 0) = [a]" 
  by(simp)

lemma tape_of_nl_cons_app1: "(<a # xs @ [b]>) = (Oc\<up>(Suc a) @ Bk # (<xs@ [b]>))"
  apply(case_tac xs; simp add: tape_of_list_def tape_of_nat_list.simps tape_of_nat_def)
  done

lemma bl_bin_bk_oc[simp]:
  "bl_bin (xs @ [Bk, Oc]) = 
  bl_bin xs + 2*2^(length xs)"
  apply(simp add: bin_wc_eq)
  using bl2nat_cons_oc[of "xs @ [Bk]"]
  apply(simp add: bl2nat_cons_bk bl2wc.simps)
  done

lemma tape_of_nat[simp]: "(<a::nat>) = Oc\<up>(Suc a)"
  apply(simp add: tape_of_nat_def)
  done

lemma tape_of_nl_cons_app2: "(<c # xs @ [b]>) = (<c # xs> @ Bk # Oc\<up>(Suc b))"
proof(induct "length xs" arbitrary: xs c, simp add: tape_of_list_def)
  fix x xs c
  assume ind: "\<And>xs c. x = length xs \<Longrightarrow> <c # xs @ [b]> = 
    <c # xs> @ Bk # Oc\<up>(Suc b)"
    and h: "Suc x = length (xs::nat list)" 
  show "<c # xs @ [b]> = <c # xs> @ Bk # Oc\<up>(Suc b)"
  proof(cases xs, simp add: tape_of_list_def)
    fix a list
    assume g: "xs = a # list"
    hence k: "<a # list @ [b]> =  <a # list> @ Bk # Oc\<up>(Suc b)"
      apply(rule_tac ind)
      using h
      apply(simp)
      done
    from g and k show "<c # xs @ [b]> = <c # xs> @ Bk # Oc\<up>(Suc b)"
      apply(simp add: tape_of_list_def)
      done
  qed
qed

lemma length_2_elems[simp]: "length (<aa # a # list>) = Suc (Suc aa) + length (<a # list>)"
  apply(simp add: tape_of_list_def)
  done

lemma bl_bin_addition[simp]: "bl_bin (Oc\<up>(Suc aa) @ Bk # tape_of_nat_list (a # lista) @ [Bk, Oc]) =
              bl_bin (Oc\<up>(Suc aa) @ Bk # tape_of_nat_list (a # lista)) + 
              2* 2^(length (Oc\<up>(Suc aa) @ Bk # tape_of_nat_list (a # lista)))"
  using bl_bin_bk_oc[of "Oc\<up>(Suc aa) @ Bk # tape_of_nat_list (a # lista)"]
  apply(simp)
  done

declare replicate_Suc[simp del]

lemma bl_bin_2[simp]: 
  "bl_bin (<aa # list>) + (4 * rs + 4) * 2 ^ (length (<aa # list>) - Suc 0)
  = bl_bin (Oc\<up>(Suc aa) @ Bk # <list @ [0]>) + rs * (2 * 2 ^ (aa + length (<list @ [0]>)))"
  apply(case_tac "list", simp add: add_mult_distrib)
  apply(simp add: tape_of_nl_cons_app2 add_mult_distrib)
  apply(simp add: tape_of_list_def)
  done

lemma tape_of_nl_app_Suc: "((<list @ [Suc ab]>)) = (<list @ [ab]>) @ [Oc]"
proof(induct list)
  case (Cons a list)
  then show ?case by(cases list;simp_all add:tape_of_list_def exp_ind)
qed (simp add: tape_of_list_def exp_ind)

lemma bl_bin_3[simp]: "bl_bin (Oc # Oc\<up>(aa) @ Bk # <list @ [ab]> @ [Oc])
              = bl_bin (Oc # Oc\<up>(aa) @ Bk # <list @ [ab]>) +
              2^(length (Oc # Oc\<up>(aa) @ Bk # <list @ [ab]>))"
  apply(simp add: bin_wc_eq)
  apply(simp add: bl2nat_cons_oc bl2wc.simps)
  using bl2nat_cons_oc[of "Oc # Oc\<up>(aa) @ Bk # <list @ [ab]>"]
  apply(simp)
  done
lemma bl_bin_4[simp]: "bl_bin (Oc # Oc\<up>(aa) @ Bk # <list @ [ab]>) + (4 * 2 ^ (aa + length (<list @ [ab]>)) +
         4 * (rs * 2 ^ (aa + length (<list @ [ab]>)))) =
       bl_bin (Oc # Oc\<up>(aa) @ Bk # <list @ [Suc ab]>) +
         rs * (2 * 2 ^ (aa + length (<list @ [Suc ab]>)))"
  apply(simp add: tape_of_nl_app_Suc)
  done

declare tape_of_nat[simp del]

fun wcode_double_case_inv :: "nat \<Rightarrow> bin_inv_t"
  where
    "wcode_double_case_inv st ires rs (l, r) = 
          (if st = Suc 0 then wcode_on_left_moving_1 ires rs (l, r)
          else if st = Suc (Suc 0) then wcode_on_checking_1 ires rs (l, r)
          else if st = 3 then wcode_erase1 ires rs (l, r)
          else if st = 4 then wcode_on_right_moving_1 ires rs (l, r)
          else if st = 5 then wcode_goon_right_moving_1 ires rs (l, r)
          else if st = 6 then wcode_backto_standard_pos ires rs (l, r)
          else if st = 13 then wcode_before_double ires rs (l, r)
          else False)"

declare wcode_double_case_inv.simps[simp del]

fun wcode_double_case_state :: "config \<Rightarrow> nat"
  where
    "wcode_double_case_state (st, l, r) = 
   13 - st"

fun wcode_double_case_step :: "config \<Rightarrow> nat"
  where
    "wcode_double_case_step (st, l, r) = 
      (if st = Suc 0 then (length l)
      else if st = Suc (Suc 0) then (length r)
      else if st = 3 then 
                 if hd r = Oc then 1 else 0
      else if st = 4 then (length r)
      else if st = 5 then (length r)
      else if st = 6 then (length l)
      else 0)"

fun wcode_double_case_measure :: "config \<Rightarrow> nat \<times> nat"
  where
    "wcode_double_case_measure (st, l, r) = 
     (wcode_double_case_state (st, l, r), 
      wcode_double_case_step (st, l, r))"

definition wcode_double_case_le :: "(config \<times> config) set"
  where "wcode_double_case_le \<equiv> (inv_image lex_pair wcode_double_case_measure)"

lemma wf_lex_pair[intro]: "wf lex_pair"
  by(auto intro:wf_lex_prod simp:lex_pair_def)

lemma wf_wcode_double_case_le[intro]: "wf wcode_double_case_le"
  by(auto intro:wf_inv_image simp: wcode_double_case_le_def )

lemma fetch_t_wcode_main[simp]:
  "fetch t_wcode_main (Suc 0) Bk = (L, Suc 0)"
  "fetch t_wcode_main (Suc 0) Oc = (L, Suc (Suc 0))"
  "fetch t_wcode_main (Suc (Suc 0)) Oc = (R, 3)"
  "fetch t_wcode_main (Suc (Suc 0)) Bk = (L, 7)"
  "fetch t_wcode_main (Suc (Suc (Suc 0))) Bk = (R, 4)"
  "fetch t_wcode_main (Suc (Suc (Suc 0))) Oc = (W0, 3)"
  "fetch t_wcode_main 4 Bk = (R, 4)"
  "fetch t_wcode_main 4 Oc = (R, 5)"
  "fetch t_wcode_main 5 Oc = (R, 5)"
  "fetch t_wcode_main 5 Bk = (W1, 6)"
  "fetch t_wcode_main 6 Bk = (R, 13)"
  "fetch t_wcode_main 6 Oc = (L, 6)"
  "fetch t_wcode_main 7 Oc = (R, 8)"
  "fetch t_wcode_main 7 Bk = (R, 0)"
  "fetch t_wcode_main 8 Bk = (R, 9)"
  "fetch t_wcode_main 9 Bk = (R, 10)"
  "fetch t_wcode_main 9 Oc = (W0, 9)"
  "fetch t_wcode_main 10 Bk = (R, 10)"
  "fetch t_wcode_main 10 Oc = (R, 11)"
  "fetch t_wcode_main 11 Bk = (W1, 12)"
  "fetch t_wcode_main 11 Oc = (R, 11)"
  "fetch t_wcode_main 12 Oc = (L, 12)"
  "fetch t_wcode_main 12 Bk = (R, t_twice_len + 14)"
  by(auto simp: t_wcode_main_def t_wcode_main_first_part_def fetch.simps numeral)

declare wcode_on_checking_1.simps[simp del]

lemmas wcode_double_case_inv_simps = 
  wcode_on_left_moving_1.simps wcode_on_left_moving_1_O.simps
  wcode_on_left_moving_1_B.simps wcode_on_checking_1.simps
  wcode_erase1.simps wcode_on_right_moving_1.simps
  wcode_goon_right_moving_1.simps wcode_backto_standard_pos.simps


lemma wcode_on_left_moving_1[simp]:
  "wcode_on_left_moving_1 ires rs (b, []) = False"
  "wcode_on_left_moving_1 ires rs (b, r) \<Longrightarrow> b \<noteq> []"
  by(auto simp: wcode_on_left_moving_1.simps wcode_on_left_moving_1_B.simps
      wcode_on_left_moving_1_O.simps)

lemma wcode_on_left_moving_1E[elim]: "\<lbrakk>wcode_on_left_moving_1 ires rs (b, Bk # list);
                tl b = aa \<and> hd b # Bk # list = ba\<rbrakk> \<Longrightarrow> 
               wcode_on_left_moving_1 ires rs (aa, ba)"
  apply(simp only: wcode_on_left_moving_1.simps wcode_on_left_moving_1_O.simps
      wcode_on_left_moving_1_B.simps)
  apply(erule_tac disjE)
   apply(erule_tac exE)+
   apply(rename_tac ml mr rn)
   apply(case_tac ml, simp)
    apply(rule_tac x = "mr - Suc (Suc 0)" in exI, rule_tac x = rn in exI)
    apply (smt One_nat_def Suc_diff_Suc append_Cons empty_replicate list.sel(3) neq0_conv replicate_Suc replicate_app_Cons_same tl_append2 tl_replicate)
   apply(rule_tac disjI1)
   apply (metis add_Suc_shift less_SucI list.exhaust_sel list.inject list.simps(3) replicate_Suc_iff_anywhere)
  by simp

declare replicate_Suc[simp]

lemma wcode_on_moving_1_Elim[elim]: 
  "\<lbrakk>wcode_on_left_moving_1 ires rs (b, Oc # list); tl b = aa \<and> hd b # Oc # list = ba\<rbrakk> 
    \<Longrightarrow> wcode_on_checking_1 ires rs (aa, ba)"
  apply(simp only: wcode_double_case_inv_simps)
  apply(erule_tac disjE)
   apply (metis cell.distinct(1) empty_replicate hd_append2 hd_replicate list.sel(1) not_gr_zero)
  apply force.

lemma wcode_on_checking_1_Elim[elim]: "\<lbrakk>wcode_on_checking_1 ires rs (b, Oc # ba);Oc # b = aa \<and> list = ba\<rbrakk>
  \<Longrightarrow> wcode_erase1 ires rs (aa, ba)"
  apply(simp only: wcode_double_case_inv_simps)
  apply(erule_tac exE)+ by auto

lemma wcode_on_checking_1_simp[simp]:
  "wcode_on_checking_1 ires rs (b, []) = False" 
  "wcode_on_checking_1 ires rs (b, Bk # list) = False"
  by(auto simp: wcode_double_case_inv_simps)

lemma wcode_erase1_nonempty_snd[simp]: "wcode_erase1 ires rs (b, []) = False"
  apply(simp add: wcode_double_case_inv_simps)
  done

lemma wcode_on_right_moving_1_nonempty_snd[simp]: "wcode_on_right_moving_1 ires rs (b, []) = False"
  apply(simp add: wcode_double_case_inv_simps)
  done

lemma wcode_on_right_moving_1_BkE[elim]:
  "\<lbrakk>wcode_on_right_moving_1 ires rs (b, Bk # ba);  Bk # b = aa \<and> list = b\<rbrakk> \<Longrightarrow> 
  wcode_on_right_moving_1 ires rs (aa, ba)"
  apply(simp only: wcode_double_case_inv_simps)
  apply(erule_tac exE)+
  apply(rename_tac ml mr rn)
  apply(rule_tac x = "Suc ml" in exI, rule_tac x = "mr - Suc 0" in exI,
      rule_tac x = rn in exI)
  apply(simp)
  apply(case_tac mr, simp, simp)
  done

lemma wcode_on_right_moving_1_OcE[elim]: 
  "\<lbrakk>wcode_on_right_moving_1 ires rs (b, Oc # ba); Oc # b = aa \<and> list = ba\<rbrakk> 
  \<Longrightarrow> wcode_goon_right_moving_1 ires rs (aa, ba)"
  apply(simp only: wcode_double_case_inv_simps)
  apply(erule_tac exE)+
  apply(rename_tac ml mr rn)
  apply(rule_tac x = "Suc 0" in exI, rule_tac x = "rs" in exI,
      rule_tac x = "ml - Suc (Suc 0)" in exI, rule_tac x = rn in exI)
  apply(case_tac mr, simp_all)
  apply(case_tac ml, simp, case_tac nat, simp, simp)
  done

lemma wcode_erase1_BkE[elim]:
  assumes "wcode_erase1 ires rs (b, Bk # ba)" "Bk # b = aa \<and> list = ba" "c = Bk # ba"
  shows "wcode_on_right_moving_1 ires rs (aa, ba)"
proof -
  from assms obtain rn ln where "b = Oc # ires"
    "tl (Bk # ba) = Bk \<up> ln @ Bk # Bk # Oc \<up> Suc rs @ Bk \<up> rn"
    unfolding wcode_double_case_inv_simps by auto
  thus ?thesis using assms(2-) unfolding wcode_double_case_inv_simps
    apply(rule_tac x = "Suc 0" in exI, rule_tac x = "Suc (Suc ln)" in exI, 
        rule_tac x = rn in exI, simp add: exp_ind del: replicate_Suc)
    done
qed

lemma wcode_erase1_OcE[elim]: "\<lbrakk>wcode_erase1 ires rs (aa, Oc # list);  b = aa \<and> Bk # list = ba\<rbrakk> \<Longrightarrow> 
  wcode_erase1 ires rs (aa, ba)"
  unfolding wcode_double_case_inv_simps
  by auto auto

lemma wcode_goon_right_moving_1_emptyE[elim]:
  assumes "wcode_goon_right_moving_1 ires rs (aa, [])" "b = aa \<and> [Oc] = ba"
  shows "wcode_backto_standard_pos ires rs (aa, ba)"
proof -
  from assms obtain ml ln rn mr where "aa = Oc \<up> ml @ Bk # Bk # Bk \<up> ln @ Oc # ires"
    "[] = Oc \<up> mr @ Bk \<up> rn" "ml + mr = Suc rs"
    by(auto simp:wcode_double_case_inv_simps)
  thus ?thesis using assms(2)
    apply(simp only: wcode_double_case_inv_simps)
    apply(rule_tac disjI2)
    apply(simp only:wcode_backto_standard_pos_O.simps)
    apply(rule_tac x = ml in exI, rule_tac x = "Suc 0" in exI, rule_tac x = ln in exI,
        rule_tac x = rn in exI, simp)
    done
qed

lemma wcode_goon_right_moving_1_BkE[elim]: 
  assumes "wcode_goon_right_moving_1 ires rs (aa, Bk # list)" "b = aa \<and> Oc # list = ba"
  shows "wcode_backto_standard_pos ires rs (aa, ba)"
proof -
  from assms obtain ln rn where "aa = Oc \<up> Suc rs @ Bk \<up> Suc (Suc ln) @ Oc # ires"
    "Bk # list = Bk \<up> rn" "b = Oc \<up> Suc rs @ Bk \<up> Suc (Suc ln) @ Oc # ires" "ba = Oc # list"
    by(auto simp:wcode_double_case_inv_simps)
  thus ?thesis using assms(2)
    apply(simp only: wcode_double_case_inv_simps wcode_backto_standard_pos_O.simps)
    apply(rule_tac disjI2)
    apply(rule exI[of _ "Suc rs"], rule exI[of _ "Suc 0"], rule_tac x = ln in exI,
        rule_tac x = "rn - Suc 0" in exI, simp)
    apply(cases rn;auto)
    done
qed

lemma wcode_goon_right_moving_1_OcE[elim]: 
  assumes "wcode_goon_right_moving_1 ires rs (b, Oc # ba)" "Oc # b = aa \<and> list = ba"
  shows "wcode_goon_right_moving_1 ires rs (aa, ba)"
proof -
  from assms obtain ml mr ln rn where
    "b = Oc \<up> ml @ Bk # Bk # Bk \<up> ln @ Oc # ires \<and>
       Oc # ba = Oc \<up> mr @ Bk \<up> rn \<and> ml + mr = Suc rs"
    unfolding wcode_double_case_inv_simps by auto
  with assms(2) show ?thesis unfolding wcode_double_case_inv_simps
    apply(rule_tac x = "Suc ml" in exI, rule_tac x = "mr - Suc 0" in exI, 
        rule_tac x = ln in exI, rule_tac x = rn in exI)
    apply(simp)
    apply(case_tac mr, simp, case_tac rn, simp_all)
    done
qed


lemma wcode_backto_standard_pos_BkE[elim]: "\<lbrakk>wcode_backto_standard_pos ires rs (b, Bk # ba); Bk # b = aa \<and> list = ba\<rbrakk> 
  \<Longrightarrow> wcode_before_double ires rs (aa, ba)"
  apply(simp only: wcode_double_case_inv_simps wcode_backto_standard_pos_B.simps
      wcode_backto_standard_pos_O.simps wcode_before_double.simps)
  apply(erule_tac disjE)
   apply(erule_tac exE)+ 
  by auto

lemma wcode_backto_standard_pos_no_Oc[simp]: "wcode_backto_standard_pos ires rs ([], Oc # list) = False"
  apply(auto simp: wcode_backto_standard_pos.simps wcode_backto_standard_pos_B.simps
      wcode_backto_standard_pos_O.simps)
  done

lemma wcode_backto_standard_pos_nonempty_snd[simp]: "wcode_backto_standard_pos ires rs (b, []) = False"
  apply(auto simp: wcode_backto_standard_pos.simps wcode_backto_standard_pos_B.simps
      wcode_backto_standard_pos_O.simps)
  done

lemma wcode_backto_standard_pos_OcE[elim]: "\<lbrakk>wcode_backto_standard_pos ires rs (b, Oc # list); tl b = aa; hd b # Oc # list =  ba\<rbrakk>
       \<Longrightarrow> wcode_backto_standard_pos ires rs (aa, ba)"
  apply(simp only:  wcode_backto_standard_pos.simps wcode_backto_standard_pos_B.simps
      wcode_backto_standard_pos_O.simps)
  apply(erule_tac disjE)
   apply(simp)
  apply(erule_tac exE)+ 
  apply(simp)
  apply (rename_tac ml mr ln rn)
  apply(case_tac ml)
   apply(rule_tac disjI1, rule_tac conjI)
    apply(rule_tac x = ln  in exI, force, rule_tac x = rn in exI, force, force).

declare nth_of.simps[simp del] fetch.simps[simp del]
lemma wcode_double_case_first_correctness:
  "let P = (\<lambda> (st, l, r). st = 13) in 
       let Q = (\<lambda> (st, l, r). wcode_double_case_inv st ires rs (l, r)) in 
       let f = (\<lambda> stp. steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Oc # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp) in
       \<exists> n .P (f n) \<and> Q (f (n::nat))"
proof -
  let ?P = "(\<lambda> (st, l, r). st = 13)"
  let ?Q = "(\<lambda> (st, l, r). wcode_double_case_inv st ires rs (l, r))"
  let ?f = "(\<lambda> stp. steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Oc # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp)"
  have "\<exists> n. ?P (?f n) \<and> ?Q (?f (n::nat))"
  proof(rule_tac halt_lemma2)
    show "wf wcode_double_case_le"
      by auto
  next
    show "\<forall> na. \<not> ?P (?f na) \<and> ?Q (?f na) \<longrightarrow>
                   ?Q (?f (Suc na)) \<and> (?f (Suc na), ?f na) \<in> wcode_double_case_le"
    proof(rule_tac allI, case_tac "?f na", simp)
      fix na a b c
      show "a \<noteq> 13 \<and> wcode_double_case_inv a ires rs (b, c) \<longrightarrow>
               (case step0 (a, b, c) t_wcode_main of (st, x) \<Rightarrow> 
                   wcode_double_case_inv st ires rs x) \<and> 
                (step0 (a, b, c) t_wcode_main, a, b, c) \<in> wcode_double_case_le"
        apply(rule_tac impI, simp add: wcode_double_case_inv.simps)
        apply(auto split: if_splits simp: step.simps, 
            case_tac [!] c, simp_all, case_tac [!] "(c::cell list)!0")
                            apply(simp_all add: wcode_double_case_inv.simps wcode_double_case_le_def
            lex_pair_def)
                      apply(auto split: if_splits)
        done
    qed
  next
    show "?Q (?f 0)"
      apply(simp add: steps.simps wcode_double_case_inv.simps 
          wcode_on_left_moving_1.simps
          wcode_on_left_moving_1_B.simps)
      apply(rule_tac disjI1)
      apply(rule_tac x = "Suc m" in exI, simp)
      apply(rule_tac x = "Suc 0" in exI, simp)
      done
  next
    show "\<not> ?P (?f 0)"
      apply(simp add: steps.simps)
      done
  qed
  thus "let P = \<lambda>(st, l, r). st = 13;
    Q = \<lambda>(st, l, r). wcode_double_case_inv st ires rs (l, r);
    f = steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Oc # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main
    in \<exists>n. P (f n) \<and> Q (f n)"
    apply(simp)
    done
qed

lemma tm_append_shift_append_steps: 
  "\<lbrakk>steps0 (st, l, r) tp stp = (st', l', r'); 
  0 < st';
  length tp1 mod 2 = 0
  \<rbrakk>
  \<Longrightarrow> steps0 (st + length tp1 div 2, l, r) (tp1 @ shift tp (length tp1 div 2) @ tp2) stp 
  = (st' + length tp1 div 2, l', r')"
proof -
  assume h: 
    "steps0 (st, l, r) tp stp = (st', l', r')"
    "0 < st'"
    "length tp1 mod 2 = 0 "
  from h have 
    "steps (st + length tp1 div 2, l, r) (tp1 @ shift tp (length tp1 div 2), 0) stp = 
                            (st' + length tp1 div 2, l', r')"
    by(rule_tac tm_append_second_steps_eq, simp_all)
  then have "steps (st + length tp1 div 2, l, r) ((tp1 @ shift tp (length tp1 div 2)) @ tp2, 0) stp = 
                            (st' + length tp1 div 2, l', r')"
    using h
    apply(rule_tac tm_append_first_steps_eq, simp_all)
    done
  thus "?thesis"
    by simp
qed 

declare start_of.simps[simp del]

lemma twice_lemma: "rec_exec rec_twice [rs] = 2*rs"
  by(auto simp: rec_twice_def rec_exec.simps)

lemma t_twice_correct: 
  "\<exists>stp ln rn. steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n)) 
  (tm_of abc_twice @ shift (mopup (Suc 0)) ((length (tm_of abc_twice) div 2))) stp =
  (0, Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (2 * rs)) @ Bk\<up>(rn))"
proof(case_tac "rec_ci rec_twice")
  fix a b c
  assume h: "rec_ci rec_twice = (a, b, c)"
  have "\<exists>stp m l. steps0 (Suc 0, Bk # Bk # ires, <[rs]> @ Bk\<up>(n)) (tm_of abc_twice @ shift (mopup (length [rs])) 
    (length (tm_of abc_twice) div 2)) stp = (0, Bk\<up>(m) @ Bk # Bk # ires, Oc\<up>(Suc (rec_exec rec_twice [rs])) @ Bk\<up>(l))"
    thm  recursive_compile_to_tm_correct1
  proof(rule_tac recursive_compile_to_tm_correct1)
    show "rec_ci rec_twice = (a, b, c)" by (simp add: h)
  next
    show "terminate rec_twice [rs]"
      apply(rule_tac primerec_terminate, auto)
      apply(simp add: rec_twice_def, auto simp: constn.simps numeral_2_eq_2)
      by(auto)
  next
    show "tm_of abc_twice = tm_of (a [+] dummy_abc (length [rs]))"
      using h
      by(simp add: abc_twice_def)
  qed
  thus "?thesis"
    apply(simp add: tape_of_list_def tape_of_nat_def rec_exec.simps twice_lemma)
    done
qed

declare adjust.simps[simp]

lemma adjust_fetch0: 
  "\<lbrakk>0 < a; a \<le> length ap div 2;  fetch ap a b = (aa, 0)\<rbrakk>
  \<Longrightarrow> fetch (adjust0 ap) a b = (aa, Suc (length ap div 2))"
  apply(case_tac b, auto simp: fetch.simps nth_of.simps nth_map
      split: if_splits)
   apply(case_tac [!] a, auto simp: fetch.simps nth_of.simps)
  done

lemma adjust_fetch_norm: 
  "\<lbrakk>st > 0;  st \<le> length tp div 2; fetch ap st b = (aa, ns); ns \<noteq> 0\<rbrakk>
 \<Longrightarrow>  fetch (adjust0 ap) st b = (aa, ns)"
  apply(case_tac b, auto simp: fetch.simps nth_of.simps nth_map
      split: if_splits)
   apply(case_tac [!] st, auto simp: fetch.simps nth_of.simps)
  done

declare adjust.simps[simp del]

lemma adjust_step_eq: 
  assumes exec: "step0 (st,l,r) ap = (st', l', r')"
    and wf_tm: "tm_wf (ap, 0)"
    and notfinal: "st' > 0"
  shows "step0 (st, l, r) (adjust0 ap) = (st', l', r')"
  using assms
proof -
  have "st > 0"
    using assms
    by(case_tac st, simp_all add: step.simps fetch.simps)
  moreover hence "st \<le> (length ap) div 2"
    using assms
    apply(case_tac "st \<le> (length ap) div 2", simp)
    apply(case_tac st, auto simp: step.simps fetch.simps)
    apply(case_tac "read r", simp_all add: fetch.simps 
        nth_of.simps adjust.simps tm_wf.simps split: if_splits)
     apply(auto simp: mod_ex2)
    done    
  ultimately have "fetch (adjust0 ap) st (read r) = fetch ap st (read r)"
    using assms
    apply(case_tac "fetch ap st (read r)")
    apply(drule_tac adjust_fetch_norm, simp_all)
    apply(simp add: step.simps)
    done
  thus "?thesis"
    using exec
    by(simp add: step.simps)
qed

declare adjust.simps[simp del]

lemma adjust_steps_eq: 
  assumes exec: "steps0 (st,l,r) ap stp = (st', l', r')"
    and wf_tm: "tm_wf (ap, 0)"
    and notfinal: "st' > 0"
  shows "steps0 (st, l, r) (adjust0 ap) stp = (st', l', r')"
  using exec notfinal
proof(induct stp arbitrary: st' l' r')
  case 0
  thus "?case"
    by(simp add: steps.simps)
next
  case (Suc stp st' l' r')
  have ind: "\<And>st' l' r'. \<lbrakk>steps0 (st, l, r) ap stp = (st', l', r'); 0 < st'\<rbrakk> 
    \<Longrightarrow> steps0 (st, l, r) (adjust0 ap) stp = (st', l', r')" by fact
  have h: "steps0 (st, l, r) ap (Suc stp) = (st', l', r')" by fact
  have g:   "0 < st'" by fact
  obtain st'' l'' r'' where a: "steps0 (st, l, r) ap stp = (st'', l'', r'')"
    by (metis prod_cases3)
  hence c:"0 < st''"
    using h g
    apply(simp add: step_red)
    apply(case_tac st'', auto)
    done
  hence b: "steps0 (st, l, r) (adjust0 ap) stp = (st'', l'', r'')"
    using a
    by(rule_tac ind, simp_all)
  thus "?case"
    using assms a b h g
    apply(simp add: step_red) 
    apply(rule_tac adjust_step_eq, simp_all)
    done
qed 

lemma adjust_halt_eq:
  assumes exec: "steps0 (1, l, r) ap stp = (0, l', r')"
    and tm_wf: "tm_wf (ap, 0)" 
  shows "\<exists> stp. steps0 (Suc 0, l, r) (adjust0 ap) stp = 
        (Suc (length ap div 2), l', r')"
proof -
  have "\<exists> stp. \<not> is_final (steps0 (1, l, r) ap stp) \<and> (steps0 (1, l, r) ap (Suc stp) = (0, l', r'))"
    using exec
    by(erule_tac before_final)
  then obtain stpa where a: 
    "\<not> is_final (steps0 (1, l, r) ap stpa) \<and> (steps0 (1, l, r) ap (Suc stpa) = (0, l', r'))" ..
  obtain sa la ra where b:"steps0 (1, l, r) ap stpa = (sa, la, ra)"  by (metis prod_cases3)
  hence c: "steps0 (Suc 0, l, r) (adjust0 ap) stpa = (sa, la, ra)"
    using assms a
    apply(rule_tac adjust_steps_eq, simp_all)
    done
  have d: "sa \<le> length ap div 2"
    using steps_in_range[of  "(l, r)" ap stpa] a tm_wf b
    by(simp)
  obtain ac ns where e: "fetch ap sa (read ra) = (ac, ns)"
    by (metis prod.exhaust)
  hence f: "ns = 0"
    using b a
    apply(simp add: step_red step.simps)
    done
  have k: "fetch (adjust0 ap) sa (read ra) = (ac, Suc (length ap div 2))"
    using a b c d e f
    apply(rule_tac adjust_fetch0, simp_all)
    done
  from a b e f k and c show "?thesis"
    apply(rule_tac x = "Suc stpa" in exI)
    apply(simp add: step_red, auto)
    apply(simp add: step.simps)
    done
qed    

declare tm_wf.simps[simp del]

lemma tm_wf_t_twice_compile [simp]: "tm_wf (t_twice_compile, 0)"
  apply(simp only: t_twice_compile_def)
  apply(rule_tac wf_tm_from_abacus, simp)
  done

lemma t_twice_change_term_state:
  "\<exists> stp ln rn. steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n)) t_twice stp
     = (Suc t_twice_len, Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (2 * rs)) @ Bk\<up>(rn))"
proof -
  have "\<exists>stp ln rn. steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n)) 
    (tm_of abc_twice @ shift (mopup (Suc 0)) ((length (tm_of abc_twice) div 2))) stp =
    (0, Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (2 * rs)) @ Bk\<up>(rn))"
    by(rule_tac t_twice_correct)
  then obtain stp ln rn where " steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n)) 
    (tm_of abc_twice @ shift (mopup (Suc 0)) ((length (tm_of abc_twice) div 2))) stp =
    (0, Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (2 * rs)) @ Bk\<up>(rn))" by blast
  hence "\<exists> stp. steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n))
    (adjust0 t_twice_compile) stp
     = (Suc (length t_twice_compile div 2), Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (2 * rs)) @ Bk\<up>(rn))"
    apply(rule_tac stp = stp in adjust_halt_eq)
     apply(simp add: t_twice_compile_def, auto)
    done
  then obtain stpb where 
    "steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n))
    (adjust0 t_twice_compile) stpb
     = (Suc (length t_twice_compile div 2), Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (2 * rs)) @ Bk\<up>(rn))" ..
  thus "?thesis"
    apply(simp add: t_twice_def t_twice_len_def)
    by metis
qed

lemma length_t_wcode_main_first_part_even[intro]: "length t_wcode_main_first_part mod 2 = 0"
  apply(auto simp: t_wcode_main_first_part_def)
  done

lemma t_twice_append_pre:
  "steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n)) t_twice stp
  = (Suc t_twice_len, Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (2 * rs)) @ Bk\<up>(rn))
   \<Longrightarrow> steps0 (Suc 0 + length t_wcode_main_first_part div 2, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n))
     (t_wcode_main_first_part @ shift t_twice (length t_wcode_main_first_part div 2) @
      ([(L, 1), (L, 1)] @ shift t_fourtimes (t_twice_len + 13) @ [(L, 1), (L, 1)])) stp 
    = (Suc (t_twice_len) + length t_wcode_main_first_part div 2, 
             Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (2 * rs)) @ Bk\<up>(rn))"
  by(rule_tac tm_append_shift_append_steps, auto)

lemma t_twice_append:
  "\<exists> stp ln rn. steps0 (Suc 0 + length t_wcode_main_first_part div 2, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n))
     (t_wcode_main_first_part @ shift t_twice (length t_wcode_main_first_part div 2) @
      ([(L, 1), (L, 1)] @ shift t_fourtimes (t_twice_len + 13) @ [(L, 1), (L, 1)])) stp 
    = (Suc (t_twice_len) + length t_wcode_main_first_part div 2, Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (2 * rs)) @ Bk\<up>(rn))"
  using t_twice_change_term_state[of ires rs n]
  apply(erule_tac exE)
  apply(erule_tac exE)
  apply(erule_tac exE)
  apply(drule_tac t_twice_append_pre)
  apply(rename_tac stp ln rn)
  apply(rule_tac x = stp in exI, rule_tac x = ln in exI, rule_tac x = rn in exI)
  apply(simp)
  done

lemma mopup_mod2: "length (mopup k) mod 2  = 0"
  by(auto simp: mopup.simps)

lemma fetch_t_wcode_main_Oc[simp]: "fetch t_wcode_main (Suc (t_twice_len + length t_wcode_main_first_part div 2)) Oc
     = (L, Suc 0)"
  apply(subgoal_tac "length (t_twice) mod 2 = 0")
   apply(simp add: t_wcode_main_def nth_append fetch.simps t_wcode_main_first_part_def 
      nth_of.simps t_twice_len_def, auto)
  apply(simp add: t_twice_def t_twice_compile_def)
  using mopup_mod2[of 1]
  apply(simp)
  done

lemma wcode_jump1: 
  "\<exists> stp ln rn. steps0 (Suc (t_twice_len) + length t_wcode_main_first_part div 2,
                       Bk\<up>(m) @ Bk # Bk # ires, Oc\<up>(Suc (2 * rs)) @ Bk\<up>(n))
     t_wcode_main stp 
    = (Suc 0, Bk\<up>(ln) @ Bk # ires, Bk # Oc\<up>(Suc (2 * rs)) @ Bk\<up>(rn))"
  apply(rule_tac x = "Suc 0" in exI, rule_tac x = "m" in exI, rule_tac x = n in exI)
  apply(simp add: steps.simps step.simps exp_ind)
  apply(case_tac m, simp_all)
  apply(simp add: exp_ind[THEN sym])
  done

lemma wcode_main_first_part_len[simp]:
  "length t_wcode_main_first_part = 24"
  apply(simp add: t_wcode_main_first_part_def)
  done

lemma wcode_double_case: 
  shows "\<exists>stp ln rn. steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Oc # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
          (Suc 0, Bk # Bk\<up>(ln) @ Oc # ires, Bk # Oc\<up>(Suc (2 * rs + 2)) @ Bk\<up>(rn))"
    (is "\<exists>stp ln rn. ?tm stp ln rn")
proof -
  from wcode_double_case_first_correctness[of ires rs m n] obtain na ln rn where
    "steps0 (Suc 0, Bk # Bk \<up> m @ Oc # Oc # ires, Bk # Oc # Oc \<up> rs @ Bk \<up> n) t_wcode_main na
      = (13, Bk # Bk # Bk \<up> ln @ Oc # ires, Oc # Oc # Oc \<up> rs @ Bk \<up> rn)"
    by(auto simp: wcode_double_case_inv.simps wcode_before_double.simps)
  hence "\<exists>stp ln rn. steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Oc # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
          (13,  Bk # Bk # Bk\<up>(ln) @ Oc # ires, Oc\<up>(Suc (Suc rs)) @ Bk\<up>(rn))"
    by(case_tac "steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Oc # ires, 
           Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main na", auto)  
  from this obtain stpa lna rna where stp1: 
    "steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Oc # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stpa = 
    (13, Bk # Bk # Bk\<up>(lna) @ Oc # ires, Oc\<up>(Suc (Suc rs)) @ Bk\<up>(rna))" by blast
  from t_twice_append[of "Bk\<up>(lna) @ Oc # ires" "Suc rs" rna] obtain stp ln rn
    where "steps0 (Suc 0 + length t_wcode_main_first_part div 2,
                   Bk # Bk # Bk \<up> lna @ Oc # ires, Oc \<up> Suc (Suc rs) @ Bk \<up> rna)
                  (t_wcode_main_first_part @ shift t_twice (length t_wcode_main_first_part div 2) @
                   [(L, 1), (L, 1)] @ shift t_fourtimes (t_twice_len + 13) @ [(L, 1), (L, 1)]) stp =
           (Suc t_twice_len + length t_wcode_main_first_part div 2, 
            Bk \<up> ln @ Bk # Bk # Bk \<up> lna @ Oc # ires, Oc \<up> Suc (2 * Suc rs) @ Bk \<up> rn)" by blast
  hence "\<exists> stp ln rn. steps0 (13, Bk # Bk # Bk\<up>(lna) @ Oc # ires, Oc\<up>(Suc (Suc rs)) @ Bk\<up>(rna)) t_wcode_main stp =
    (13 + t_twice_len, Bk # Bk # Bk\<up>(ln) @ Oc # ires, Oc\<up>(Suc (Suc (Suc (2 *rs)))) @ Bk\<up>(rn))"
    using t_twice_append[of "Bk\<up>(lna) @ Oc # ires" "Suc rs" rna]
    apply(simp)
    apply(rule_tac x = stp in exI, rule_tac x = "ln + lna" in exI, 
        rule_tac x = rn in exI)
    apply(simp add: t_wcode_main_def)
    apply(simp add: replicate_Suc[THEN sym] replicate_add [THEN sym] del: replicate_Suc)
    done
  from this obtain stpb lnb rnb where stp2: 
    "steps0 (13, Bk # Bk # Bk\<up>(lna) @ Oc # ires, Oc\<up>(Suc (Suc rs)) @ Bk\<up>(rna)) t_wcode_main stpb =
    (13 + t_twice_len, Bk # Bk # Bk\<up>(lnb) @ Oc # ires, Oc\<up>(Suc (Suc (Suc (2 *rs)))) @ Bk\<up>(rnb))" by blast
  from wcode_jump1[of lnb "Oc # ires" "Suc rs" rnb] obtain stp ln rn where
    "steps0 (Suc t_twice_len + length t_wcode_main_first_part div 2, 
             Bk \<up> lnb @ Bk # Bk # Oc # ires, Oc \<up> Suc (2 * Suc rs) @ Bk \<up> rnb) t_wcode_main stp =
     (Suc 0, Bk \<up> ln @ Bk # Oc # ires, Bk # Oc \<up> Suc (2 * Suc rs) @ Bk \<up> rn)" by metis
  hence "steps0 (13 + t_twice_len, Bk # Bk # Bk\<up>(lnb) @ Oc # ires,
    Oc\<up>(Suc (Suc (Suc (2 *rs)))) @ Bk\<up>(rnb)) t_wcode_main stp = 
       (Suc 0,  Bk # Bk\<up>(ln) @ Oc # ires, Bk # Oc\<up>(Suc (Suc (Suc (2 *rs)))) @ Bk\<up>(rn))"
    apply(auto simp add: t_wcode_main_def)
    apply(subgoal_tac "Bk\<up>(lnb) @ Bk # Bk # Oc # ires = Bk # Bk # Bk\<up>(lnb) @ Oc # ires", simp)
     apply(simp add: replicate_Suc[THEN sym] exp_ind[THEN sym] del: replicate_Suc)
    apply(simp)
    apply(simp add: replicate_Suc[THEN sym] exp_ind del: replicate_Suc)
    done 
  hence "\<exists>stp ln rn. steps0 (13 + t_twice_len, Bk # Bk # Bk\<up>(lnb) @ Oc # ires,
    Oc\<up>(Suc (Suc (Suc (2 *rs)))) @ Bk\<up>(rnb)) t_wcode_main stp = 
       (Suc 0,  Bk # Bk\<up>(ln) @ Oc # ires, Bk # Oc\<up>(Suc (Suc (Suc (2 *rs)))) @ Bk\<up>(rn))"
    by blast
  from this obtain stpc lnc rnc where stp3: 
    "steps0 (13 + t_twice_len, Bk # Bk # Bk\<up>(lnb) @ Oc # ires,
    Oc\<up>(Suc (Suc (Suc (2 *rs)))) @ Bk\<up>(rnb)) t_wcode_main stpc = 
       (Suc 0,  Bk # Bk\<up>(lnc) @ Oc # ires, Bk # Oc\<up>(Suc (Suc (Suc (2 *rs)))) @ Bk\<up>(rnc))"
    by blast
  from stp1 stp2 stp3 have "?tm (stpa + stpb + stpc) lnc rnc" by simp
  thus "?thesis" by blast
qed


(* Begin: fourtime_case*)
fun wcode_on_left_moving_2_B :: "bin_inv_t"
  where
    "wcode_on_left_moving_2_B ires rs (l, r) =
     (\<exists> ml mr rn. l = Bk\<up>(ml) @ Oc # Bk # Oc # ires \<and>
                 r = Bk\<up>(mr) @ Oc\<up>(Suc rs) @ Bk\<up>(rn) \<and> 
                 ml + mr > Suc 0 \<and> mr > 0)"

fun wcode_on_left_moving_2_O :: "bin_inv_t"
  where
    "wcode_on_left_moving_2_O ires rs (l, r) =
     (\<exists> ln rn. l = Bk # Oc # ires \<and>
               r = Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

fun wcode_on_left_moving_2 :: "bin_inv_t"
  where
    "wcode_on_left_moving_2 ires rs (l, r) = 
      (wcode_on_left_moving_2_B ires rs (l, r) \<or> 
      wcode_on_left_moving_2_O ires rs (l, r))"

fun wcode_on_checking_2 :: "bin_inv_t"
  where
    "wcode_on_checking_2 ires rs (l, r) =
       (\<exists> ln rn. l = Oc#ires \<and> 
                 r = Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

fun wcode_goon_checking :: "bin_inv_t"
  where
    "wcode_goon_checking ires rs (l, r) =
       (\<exists> ln rn. l = ires \<and>
                 r = Oc # Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

fun wcode_right_move :: "bin_inv_t"
  where
    "wcode_right_move ires rs (l, r) = 
     (\<exists> ln rn. l = Oc # ires \<and>
                 r = Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

fun wcode_erase2 :: "bin_inv_t"
  where
    "wcode_erase2 ires rs (l, r) = 
        (\<exists> ln rn. l = Bk # Oc # ires \<and>
                 tl r = Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

fun wcode_on_right_moving_2 :: "bin_inv_t"
  where
    "wcode_on_right_moving_2 ires rs (l, r) = 
        (\<exists> ml mr rn. l = Bk\<up>(ml) @ Oc # ires \<and> 
                     r = Bk\<up>(mr) @ Oc\<up>(Suc rs) @ Bk\<up>(rn) \<and> ml + mr > Suc 0)"

fun wcode_goon_right_moving_2 :: "bin_inv_t"
  where
    "wcode_goon_right_moving_2 ires rs (l, r) = 
        (\<exists> ml mr ln rn. l = Oc\<up>(ml) @ Bk # Bk # Bk\<up>(ln) @ Oc # ires \<and>
                        r = Oc\<up>(mr) @ Bk\<up>(rn) \<and> ml + mr = Suc rs)"

fun wcode_backto_standard_pos_2_B :: "bin_inv_t"
  where
    "wcode_backto_standard_pos_2_B ires rs (l, r) = 
           (\<exists> ln rn. l = Bk # Bk\<up>(ln) @ Oc # ires \<and> 
                     r = Bk # Oc\<up>(Suc (Suc rs)) @ Bk\<up>(rn))"

fun wcode_backto_standard_pos_2_O :: "bin_inv_t"
  where
    "wcode_backto_standard_pos_2_O ires rs (l, r) = 
          (\<exists> ml mr ln rn. l = Oc\<up>(ml )@ Bk # Bk # Bk\<up>(ln) @ Oc # ires \<and> 
                          r = Oc\<up>(mr) @ Bk\<up>(rn) \<and> 
                          ml + mr = (Suc (Suc rs)) \<and> mr > 0)"

fun wcode_backto_standard_pos_2 :: "bin_inv_t"
  where
    "wcode_backto_standard_pos_2 ires rs (l, r) = 
           (wcode_backto_standard_pos_2_O ires rs (l, r) \<or> 
           wcode_backto_standard_pos_2_B ires rs (l, r))"

fun wcode_before_fourtimes :: "bin_inv_t"
  where
    "wcode_before_fourtimes ires rs (l, r) = 
          (\<exists> ln rn. l = Bk # Bk # Bk\<up>(ln) @ Oc # ires \<and> 
                    r = Oc\<up>(Suc (Suc rs)) @ Bk\<up>(rn))"

declare wcode_on_left_moving_2_B.simps[simp del] wcode_on_left_moving_2.simps[simp del]
  wcode_on_left_moving_2_O.simps[simp del] wcode_on_checking_2.simps[simp del]
  wcode_goon_checking.simps[simp del] wcode_right_move.simps[simp del]
  wcode_erase2.simps[simp del]
  wcode_on_right_moving_2.simps[simp del] wcode_goon_right_moving_2.simps[simp del]
  wcode_backto_standard_pos_2_B.simps[simp del] wcode_backto_standard_pos_2_O.simps[simp del]
  wcode_backto_standard_pos_2.simps[simp del]

lemmas wcode_fourtimes_invs = 
  wcode_on_left_moving_2_B.simps wcode_on_left_moving_2.simps
  wcode_on_left_moving_2_O.simps wcode_on_checking_2.simps
  wcode_goon_checking.simps wcode_right_move.simps
  wcode_erase2.simps
  wcode_on_right_moving_2.simps wcode_goon_right_moving_2.simps
  wcode_backto_standard_pos_2_B.simps wcode_backto_standard_pos_2_O.simps
  wcode_backto_standard_pos_2.simps

fun wcode_fourtimes_case_inv :: "nat \<Rightarrow> bin_inv_t"
  where
    "wcode_fourtimes_case_inv st ires rs (l, r) = 
           (if st = Suc 0 then wcode_on_left_moving_2 ires rs (l, r)
            else if st = Suc (Suc 0) then wcode_on_checking_2 ires rs (l, r)
            else if st = 7 then wcode_goon_checking ires rs (l, r)
            else if st = 8 then wcode_right_move ires rs (l, r)
            else if st = 9 then wcode_erase2 ires rs (l, r)
            else if st = 10 then wcode_on_right_moving_2 ires rs (l, r)
            else if st = 11 then wcode_goon_right_moving_2 ires rs (l, r)
            else if st = 12 then wcode_backto_standard_pos_2 ires rs (l, r)
            else if st = t_twice_len + 14 then wcode_before_fourtimes ires rs (l, r)
            else False)"

declare wcode_fourtimes_case_inv.simps[simp del]

fun wcode_fourtimes_case_state :: "config \<Rightarrow> nat"
  where
    "wcode_fourtimes_case_state (st, l, r) = 13 - st"

fun wcode_fourtimes_case_step :: "config \<Rightarrow> nat"
  where
    "wcode_fourtimes_case_step (st, l, r) = 
         (if st = Suc 0 then length l
          else if st = 9 then 
           (if hd r = Oc then 1
            else 0)
          else if st = 10 then length r
          else if st = 11 then length r
          else if st = 12 then length l
          else 0)"

fun wcode_fourtimes_case_measure :: "config \<Rightarrow> nat \<times> nat"
  where
    "wcode_fourtimes_case_measure (st, l, r) = 
     (wcode_fourtimes_case_state (st, l, r), 
      wcode_fourtimes_case_step (st, l, r))"

definition wcode_fourtimes_case_le :: "(config \<times> config) set"
  where "wcode_fourtimes_case_le \<equiv> (inv_image lex_pair wcode_fourtimes_case_measure)"

lemma wf_wcode_fourtimes_case_le[intro]: "wf wcode_fourtimes_case_le"
  by(auto simp: wcode_fourtimes_case_le_def)

lemma nonempty_snd [simp]:
  "wcode_on_left_moving_2 ires rs (b, []) = False"
  "wcode_on_checking_2 ires rs (b, []) = False"
  "wcode_goon_checking ires rs (b, []) = False"
  "wcode_right_move ires rs (b, []) = False"
  "wcode_erase2 ires rs (b, []) = False"
  "wcode_on_right_moving_2 ires rs (b, []) = False"
  "wcode_backto_standard_pos_2 ires rs (b, []) = False"
  "wcode_on_checking_2 ires rs (b, Oc # list) = False"
  by(auto simp: wcode_fourtimes_invs) 

lemma wcode_on_left_moving_2[simp]:
  "wcode_on_left_moving_2 ires rs (b, Bk # list) \<Longrightarrow>  wcode_on_left_moving_2 ires rs (tl b, hd b # Bk # list)"
  apply(simp only: wcode_fourtimes_invs)
  apply(erule_tac disjE)
   apply(erule_tac exE)+
   apply(simp add: gr1_conv_Suc exp_ind replicate_app_Cons_same split:hd_repeat_cases)
   apply (auto simp add: gr0_conv_Suc[symmetric] replicate_app_Cons_same split:hd_repeat_cases)
  by force+


lemma wcode_goon_checking_via_2 [simp]: "wcode_on_checking_2 ires rs (b, Bk # list)
       \<Longrightarrow>   wcode_goon_checking ires rs (tl b, hd b # Bk # list)"
  unfolding wcode_fourtimes_invs by auto

lemma wcode_erase2_via_move [simp]: "wcode_right_move ires rs (b, Bk # list) \<Longrightarrow>  wcode_erase2 ires rs (Bk # b, list)"
  by (auto simp:wcode_fourtimes_invs ) auto

lemma wcode_on_right_moving_2_via_erase2[simp]:
  "wcode_erase2 ires rs (b, Bk # list) \<Longrightarrow> wcode_on_right_moving_2 ires rs (Bk # b, list)"
  apply(auto simp:wcode_fourtimes_invs )
  apply(rule_tac x = "Suc (Suc 0)" in exI, simp add: exp_ind)
  by (metis replicate_Suc_iff_anywhere replicate_app_Cons_same)

lemma wcode_on_right_moving_2_move_Bk[simp]: "wcode_on_right_moving_2 ires rs (b, Bk # list)
       \<Longrightarrow> wcode_on_right_moving_2 ires rs (Bk # b, list)"
  apply(auto simp: wcode_fourtimes_invs) apply(rename_tac ml mr rn)
  apply(rule_tac x = "Suc ml" in exI, simp)
  apply(rule_tac x = "mr - 1" in exI, case_tac mr,auto)
  done

lemma wcode_backto_standard_pos_2_via_right[simp]:
  "wcode_goon_right_moving_2 ires rs (b, Bk # list) \<Longrightarrow> 
                 wcode_backto_standard_pos_2 ires rs (b, Oc # list)"
  apply(simp add: wcode_fourtimes_invs, auto)
  by (metis add.right_neutral add_Suc_shift append_Cons list.sel(3)
      replicate.simps(1) replicate_Suc replicate_Suc_iff_anywhere self_append_conv2
      tl_replicate zero_less_Suc)

lemma wcode_on_checking_2_via_left[simp]: "wcode_on_left_moving_2 ires rs (b, Oc # list) \<Longrightarrow> 
                     wcode_on_checking_2 ires rs (tl b, hd b # Oc # list)"
  by(auto simp: wcode_fourtimes_invs)

lemma wcode_backto_standard_pos_2_empty_via_right[simp]:
  "wcode_goon_right_moving_2 ires rs (b, []) \<Longrightarrow>
              wcode_backto_standard_pos_2 ires rs (b, [Oc])"
  apply(simp only: wcode_fourtimes_invs)
  apply(erule_tac exE)+
  by(rule_tac disjI1,auto)

lemma wcode_goon_checking_cases[simp]: "wcode_goon_checking ires rs (b, Oc # list) \<Longrightarrow>
  (b = [] \<longrightarrow> wcode_right_move ires rs ([Oc], list)) \<and>
  (b \<noteq> [] \<longrightarrow> wcode_right_move ires rs (Oc # b, list))"
  apply(simp only: wcode_fourtimes_invs)
  apply(erule_tac exE)+
  apply(auto)
  done

lemma wcode_right_move_no_Oc[simp]: "wcode_right_move ires rs (b, Oc # list) = False"
  apply(auto simp: wcode_fourtimes_invs)
  done

lemma wcode_erase2_Bk_via_Oc[simp]: "wcode_erase2 ires rs (b, Oc # list)
       \<Longrightarrow> wcode_erase2 ires rs (b, Bk # list)"
  apply(auto simp: wcode_fourtimes_invs)
  done

lemma wcode_goon_right_moving_2_Oc_move[simp]:
  "wcode_on_right_moving_2 ires rs (b, Oc # list)
       \<Longrightarrow> wcode_goon_right_moving_2 ires rs (Oc # b, list)"
  apply(auto simp: wcode_fourtimes_invs)
  apply(rule_tac x = "Suc 0" in exI, auto)
  apply(rule_tac x = "ml - 2" in exI)
  apply(case_tac ml, simp, case_tac "ml - 1", simp_all)
  done

lemma wcode_backto_standard_pos_2_exists[simp]: "wcode_backto_standard_pos_2 ires rs (b, Bk # list)
       \<Longrightarrow> (\<exists>ln. b = Bk # Bk\<up>(ln) @ Oc # ires) \<and> (\<exists>rn. list = Oc\<up>(Suc (Suc rs)) @ Bk\<up>(rn))"
  by(simp add: wcode_fourtimes_invs)

lemma wcode_goon_right_moving_2_move_Oc[simp]: "wcode_goon_right_moving_2 ires rs (b, Oc # list) \<Longrightarrow>
       wcode_goon_right_moving_2 ires rs (Oc # b, list)"
  apply(simp only:wcode_fourtimes_invs, auto)
  apply(rename_tac ml ln mr rn)
  apply(case_tac mr;force)
  done


lemma wcode_backto_standard_pos_2_Oc_mv_hd[simp]:
  "wcode_backto_standard_pos_2 ires rs (b, Oc # list)    
            \<Longrightarrow> wcode_backto_standard_pos_2 ires rs (tl b, hd b # Oc # list)"
  apply(simp only: wcode_fourtimes_invs)
  apply(erule_tac disjE)
   apply(erule_tac exE)+ apply(rename_tac ml mr ln rn)
  by (case_tac ml, force,force,force)

lemma nonempty_fst[simp]:
  "wcode_on_left_moving_2 ires rs (b, Bk # list) \<Longrightarrow> b \<noteq> []"
  "wcode_on_checking_2 ires rs (b, Bk # list) \<Longrightarrow> b \<noteq> []"
  "wcode_goon_checking ires rs (b, Bk # list) = False"
  "wcode_right_move ires rs (b, Bk # list) \<Longrightarrow> b\<noteq> []" 
  "wcode_erase2 ires rs (b, Bk # list) \<Longrightarrow> b \<noteq> []"
  "wcode_on_right_moving_2 ires rs (b, Bk # list) \<Longrightarrow> b \<noteq> []"
  "wcode_goon_right_moving_2 ires rs (b, Bk # list) \<Longrightarrow> b \<noteq> []"
  "wcode_backto_standard_pos_2 ires rs (b, Bk # list) \<Longrightarrow>  b \<noteq> []"
  "wcode_on_left_moving_2 ires rs (b, Oc # list) \<Longrightarrow> b \<noteq> []"
  "wcode_goon_right_moving_2 ires rs (b, []) \<Longrightarrow> b \<noteq> []"
  "wcode_erase2 ires rs (b, Oc # list) \<Longrightarrow> b \<noteq> []"
  "wcode_on_right_moving_2 ires rs (b, Oc # list) \<Longrightarrow> b \<noteq> []"
  "wcode_goon_right_moving_2 ires rs (b, Oc # list) \<Longrightarrow> b \<noteq> []"
  "wcode_backto_standard_pos_2 ires rs (b, Oc # list) \<Longrightarrow> b \<noteq> []"
  by(auto simp: wcode_fourtimes_invs)


lemma wcode_fourtimes_case_first_correctness:
  shows "let P = (\<lambda> (st, l, r). st = t_twice_len + 14) in 
  let Q = (\<lambda> (st, l, r). wcode_fourtimes_case_inv st ires rs (l, r)) in 
  let f = (\<lambda> stp. steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # Oc # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp) in
  \<exists> n .P (f n) \<and> Q (f (n::nat))"
proof -
  let ?P = "(\<lambda> (st, l, r). st = t_twice_len + 14)"
  let ?Q = "(\<lambda> (st, l, r). wcode_fourtimes_case_inv st ires rs (l, r))"
  let ?f = "(\<lambda> stp. steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # Oc # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp)"
  have "\<exists> n . ?P (?f n) \<and> ?Q (?f (n::nat))"
  proof(rule_tac halt_lemma2)
    show "wf wcode_fourtimes_case_le"
      by auto
  next
    have "\<not> ?P (?f na) \<and> ?Q (?f na) \<longrightarrow>
                  ?Q (?f (Suc na)) \<and> (?f (Suc na), ?f na) \<in> wcode_fourtimes_case_le" for na
      apply(cases "?f na", rule_tac impI)
      apply(simp add: step_red step.simps)
      apply(case_tac "snd (snd (?f na))", simp, case_tac [2] "hd (snd (snd (?f na)))", simp_all)
        apply(simp_all add: wcode_fourtimes_case_inv.simps
          wcode_fourtimes_case_le_def lex_pair_def split: if_splits)
      by(auto simp: wcode_backto_standard_pos_2.simps wcode_backto_standard_pos_2_O.simps
          wcode_backto_standard_pos_2_B.simps gr0_conv_Suc)
    thus "\<forall> na. \<not> ?P (?f na) \<and> ?Q (?f na) \<longrightarrow>
                  ?Q (?f (Suc na)) \<and> (?f (Suc na), ?f na) \<in> wcode_fourtimes_case_le" by auto
  next
    show "?Q (?f 0)"
      apply(simp add: steps.simps wcode_fourtimes_case_inv.simps)
      apply(simp add: wcode_on_left_moving_2.simps wcode_on_left_moving_2_B.simps 
          wcode_on_left_moving_2_O.simps)
      apply(rule_tac x = "Suc m" in exI, simp )
      apply(rule_tac x ="Suc 0" in exI, auto)
      done
  next
    show "\<not> ?P (?f 0)"
      apply(simp add: steps.simps)
      done
  qed
  thus "?thesis"
    apply(erule_tac exE, simp)
    done
qed

definition t_fourtimes_len :: "nat"
  where
    "t_fourtimes_len = (length t_fourtimes div 2)"

lemma primerec_rec_fourtimes_1[intro]: "primerec rec_fourtimes (Suc 0)"
  apply(auto simp: rec_fourtimes_def numeral_4_eq_4 constn.simps)
  by auto

lemma fourtimes_lemma: "rec_exec rec_fourtimes [rs] = 4 * rs"
  by(simp add: rec_exec.simps rec_fourtimes_def)

lemma t_fourtimes_correct: 
  "\<exists>stp ln rn. steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n)) 
    (tm_of abc_fourtimes @ shift (mopup 1) (length (tm_of abc_fourtimes) div 2)) stp =
       (0, Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (4 * rs)) @ Bk\<up>(rn))"
proof(case_tac "rec_ci rec_fourtimes")
  fix a b c
  assume h: "rec_ci rec_fourtimes = (a, b, c)"
  have "\<exists>stp m l. steps0 (Suc 0, Bk # Bk # ires, <[rs]> @ Bk\<up>(n)) (tm_of abc_fourtimes @ shift (mopup (length [rs])) 
    (length (tm_of abc_fourtimes) div 2)) stp = (0, Bk\<up>(m) @ Bk # Bk # ires, Oc\<up>(Suc (rec_exec rec_fourtimes [rs])) @ Bk\<up>(l))"
    thm recursive_compile_to_tm_correct1
  proof(rule_tac recursive_compile_to_tm_correct1)
    show "rec_ci rec_fourtimes = (a, b, c)" by (simp add: h)
  next
    show "terminate rec_fourtimes [rs]"
      apply(rule_tac primerec_terminate)
      by auto
  next
    show "tm_of abc_fourtimes = tm_of (a [+] dummy_abc (length [rs]))"
      using h
      by(simp add: abc_fourtimes_def)
  qed
  thus "?thesis"
    apply(simp add: tape_of_list_def tape_of_nat_def fourtimes_lemma)
    done
qed

lemma wf_fourtimes[intro]: "tm_wf (t_fourtimes_compile, 0)"
  apply(simp only: t_fourtimes_compile_def)
  apply(rule_tac wf_tm_from_abacus, simp)
  done

lemma t_fourtimes_change_term_state:
  "\<exists> stp ln rn. steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n)) t_fourtimes stp
     = (Suc t_fourtimes_len, Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (4 * rs)) @ Bk\<up>(rn))"
proof -
  have "\<exists>stp ln rn. steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n)) 
    (tm_of abc_fourtimes @ shift (mopup 1) ((length (tm_of abc_fourtimes) div 2))) stp =
    (0, Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (4 * rs)) @ Bk\<up>(rn))"
    by(rule_tac t_fourtimes_correct)
  then obtain stp ln rn where 
    "steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n)) 
    (tm_of abc_fourtimes @ shift (mopup 1) ((length (tm_of abc_fourtimes) div 2))) stp =
    (0, Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (4 * rs)) @ Bk\<up>(rn))" by blast
  hence "\<exists> stp. steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n))
    (adjust0 t_fourtimes_compile) stp
     = (Suc (length t_fourtimes_compile div 2), Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (4 * rs)) @ Bk\<up>(rn))"
    apply(rule_tac stp = stp in adjust_halt_eq)
     apply(simp add: t_fourtimes_compile_def, auto)
    done
  then obtain stpb where 
    "steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n))
    (adjust0 t_fourtimes_compile) stpb
     = (Suc (length t_fourtimes_compile div 2), Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (4 * rs)) @ Bk\<up>(rn))" ..
  thus "?thesis"
    apply(simp add: t_fourtimes_def t_fourtimes_len_def)
    by metis
qed

lemma length_t_twice_even[intro]: "is_even (length t_twice)"
  by(auto simp: t_twice_def t_twice_compile_def intro!:mopup_mod2)

lemma t_fourtimes_append_pre:
  "steps0 (Suc 0, Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n)) t_fourtimes stp
  = (Suc t_fourtimes_len, Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (4 * rs)) @ Bk\<up>(rn))
   \<Longrightarrow> steps0 (Suc 0 + length (t_wcode_main_first_part @ 
              shift t_twice (length t_wcode_main_first_part div 2) @ [(L, 1), (L, 1)]) div 2,
       Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n))
     ((t_wcode_main_first_part @ 
  shift t_twice (length t_wcode_main_first_part div 2) @ [(L, 1), (L, 1)]) @ 
  shift t_fourtimes (length (t_wcode_main_first_part @ 
  shift t_twice (length t_wcode_main_first_part div 2) @ [(L, 1), (L, 1)]) div 2) @ ([(L, 1), (L, 1)])) stp 
  = ((Suc t_fourtimes_len) + length (t_wcode_main_first_part @ 
  shift t_twice (length t_wcode_main_first_part div 2) @ [(L, 1), (L, 1)]) div 2,
  Bk\<up>(ln) @ Bk # Bk # ires, Oc\<up>(Suc (4 * rs)) @ Bk\<up>(rn))"
  using length_t_twice_even
  by(intro tm_append_shift_append_steps, auto)

lemma split_26_even[simp]: "(26 + l::nat) div 2 = l div 2 + 13" by(simp)

lemma t_twice_len_plust_14[simp]: "t_twice_len + 14 =  14 + length (shift t_twice 12) div 2"
  apply(simp add: t_twice_def t_twice_len_def)
  done

lemma t_fourtimes_append:
  "\<exists> stp ln rn. 
  steps0 (Suc 0 + length (t_wcode_main_first_part @ shift t_twice
  (length t_wcode_main_first_part div 2) @ [(L, 1), (L, 1)]) div 2, 
  Bk # Bk # ires, Oc\<up>(Suc rs) @ Bk\<up>(n))
  ((t_wcode_main_first_part @ shift t_twice (length t_wcode_main_first_part div 2) @
  [(L, 1), (L, 1)]) @ shift t_fourtimes (t_twice_len + 13) @ [(L, 1), (L, 1)]) stp 
  = (Suc t_fourtimes_len + length (t_wcode_main_first_part @ shift t_twice
  (length t_wcode_main_first_part div 2) @ [(L, 1), (L, 1)]) div 2, Bk\<up>(ln) @ Bk # Bk # ires,
                                                                 Oc\<up>(Suc (4 * rs)) @ Bk\<up>(rn))"
  using t_fourtimes_change_term_state[of ires rs n]
  apply(erule_tac exE)
  apply(erule_tac exE)
  apply(erule_tac exE)
  apply(drule_tac t_fourtimes_append_pre)
  apply(rule_tac x = stp in exI, rule_tac x = ln in exI, rule_tac x = rn in exI)
  apply(simp add: t_twice_len_def)
  done

lemma even_fourtimes_len: "length t_fourtimes mod 2 = 0"
  apply(auto simp: t_fourtimes_def t_fourtimes_compile_def)
  by (metis mopup_mod2)

lemma t_twice_even[simp]: "2 * (length t_twice div 2) = length t_twice"
  using length_t_twice_even by arith

lemma t_fourtimes_even[simp]: "2 * (length t_fourtimes div 2) = length t_fourtimes"
  using even_fourtimes_len
  by arith

lemma fetch_t_wcode_14_Oc: "fetch t_wcode_main (14 + length t_twice div 2 + t_fourtimes_len) Oc
             = (L, Suc 0)" 
  apply(subgoal_tac "14 = Suc 13")
   apply(simp only: fetch.simps add_Suc nth_of.simps t_wcode_main_def)
   apply(simp add:length_t_twice_even t_fourtimes_len_def nth_append)
  by arith

lemma fetch_t_wcode_14_Bk: "fetch t_wcode_main (14 + length t_twice div 2 + t_fourtimes_len) Bk
             = (L, Suc 0)"
  apply(subgoal_tac "14 = Suc 13")
   apply(simp only: fetch.simps add_Suc nth_of.simps t_wcode_main_def)
   apply(simp add:length_t_twice_even t_fourtimes_len_def nth_append)
  by arith

lemma fetch_t_wcode_14 [simp]: "fetch t_wcode_main (14 + length t_twice div 2 + t_fourtimes_len) b
             = (L, Suc 0)"
  apply(case_tac b, simp_all add:fetch_t_wcode_14_Bk fetch_t_wcode_14_Oc)
  done

lemma wcode_jump2: 
  "\<exists> stp ln rn. steps0 (t_twice_len + 14 + t_fourtimes_len
  , Bk # Bk # Bk\<up>(lnb) @ Oc # ires, Oc\<up>(Suc (4 * rs + 4)) @ Bk\<up>(rnb)) t_wcode_main stp =
  (Suc 0, Bk # Bk\<up>(ln) @ Oc # ires, Bk # Oc\<up>(Suc (4 * rs + 4)) @ Bk\<up>(rn))"
  apply(rule_tac x = "Suc 0" in exI)
  apply(simp add: steps.simps)
  apply(rule_tac x = lnb in exI, rule_tac x = rnb in exI)
  apply(simp add: step.simps)
  done

lemma wcode_fourtimes_case:
  shows "\<exists>stp ln rn.
  steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # Oc # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
  (Suc 0, Bk # Bk\<up>(ln) @ Oc # ires, Bk # Oc\<up>(Suc (4*rs + 4)) @ Bk\<up>(rn))"
proof -
  have "\<exists>stp ln rn.
  steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # Oc # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
  (t_twice_len + 14, Bk # Bk # Bk\<up>(ln) @ Oc # ires, Oc\<up>(Suc (rs + 1)) @ Bk\<up>(rn))"
    using wcode_fourtimes_case_first_correctness[of ires rs m n]
    by (auto simp add: wcode_fourtimes_case_inv.simps) auto
  from this obtain stpa lna rna where stp1:
    "steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # Oc # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stpa =
  (t_twice_len + 14, Bk # Bk # Bk\<up>(lna) @ Oc # ires, Oc\<up>(Suc (rs + 1)) @ Bk\<up>(rna))" by blast
  have "\<exists>stp ln rn. steps0 (t_twice_len + 14, Bk # Bk # Bk\<up>(lna) @ Oc # ires, Oc\<up>(Suc (rs + 1)) @ Bk\<up>(rna))
                     t_wcode_main stp =
          (t_twice_len + 14 + t_fourtimes_len, Bk # Bk # Bk\<up>(ln) @ Oc # ires,  Oc\<up>(Suc (4*rs + 4)) @ Bk\<up>(rn))"
    using t_fourtimes_append[of " Bk\<up>(lna) @ Oc # ires" "rs + 1" rna]
    apply(erule_tac exE)
    apply(erule_tac exE)
    apply(erule_tac exE)
    apply(simp add: t_wcode_main_def) apply(rename_tac stp ln rn)
    apply(rule_tac x = stp in exI, 
        rule_tac x = "ln + lna" in exI,
        rule_tac x = rn in exI, simp)
    apply(simp add: replicate_Suc[THEN sym] replicate_add[THEN sym] del: replicate_Suc)
    done
  from this obtain stpb lnb rnb where stp2:
    "steps0 (t_twice_len + 14, Bk # Bk # Bk\<up>(lna) @ Oc # ires, Oc\<up>(Suc (rs + 1)) @ Bk\<up>(rna))
                     t_wcode_main stpb =
       (t_twice_len + 14 + t_fourtimes_len, Bk # Bk # Bk\<up>(lnb) @ Oc # ires,  Oc\<up>(Suc (4*rs + 4)) @ Bk\<up>(rnb))"
    by blast
  have "\<exists>stp ln rn. steps0 (t_twice_len + 14 + t_fourtimes_len,
    Bk # Bk # Bk\<up>(lnb) @ Oc # ires,  Oc\<up>(Suc (4*rs + 4)) @ Bk\<up>(rnb))
    t_wcode_main stp =
    (Suc 0, Bk # Bk\<up>(ln) @ Oc # ires, Bk # Oc\<up>(Suc (4*rs + 4)) @ Bk\<up>(rn))"
    apply(rule wcode_jump2)
    done
  from this obtain stpc lnc rnc where stp3: 
    "steps0 (t_twice_len + 14 + t_fourtimes_len,
    Bk # Bk # Bk\<up>(lnb) @ Oc # ires,  Oc\<up>(Suc (4*rs + 4)) @ Bk\<up>(rnb))
    t_wcode_main stpc =
    (Suc 0, Bk # Bk\<up>(lnc) @ Oc # ires, Bk # Oc\<up>(Suc (4*rs + 4)) @ Bk\<up>(rnc))"
    by blast
  from stp1 stp2 stp3 show "?thesis"
    apply(rule_tac x = "stpa + stpb + stpc" in exI,
        rule_tac x = lnc in exI, rule_tac x = rnc in exI)
    apply(simp)
    done
qed

fun wcode_on_left_moving_3_B :: "bin_inv_t"
  where
    "wcode_on_left_moving_3_B ires rs (l, r) = 
       (\<exists> ml mr rn. l = Bk\<up>(ml) @ Oc # Bk # Bk # ires \<and>
                    r = Bk\<up>(mr) @ Oc\<up>(Suc rs) @ Bk\<up>(rn) \<and> 
                    ml + mr > Suc 0 \<and> mr > 0 )"

fun wcode_on_left_moving_3_O :: "bin_inv_t"
  where
    "wcode_on_left_moving_3_O ires rs (l, r) = 
         (\<exists> ln rn. l = Bk # Bk # ires \<and>
                   r = Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

fun wcode_on_left_moving_3 :: "bin_inv_t"
  where
    "wcode_on_left_moving_3 ires rs (l, r) = 
       (wcode_on_left_moving_3_B ires rs (l, r) \<or>  
        wcode_on_left_moving_3_O ires rs (l, r))"

fun wcode_on_checking_3 :: "bin_inv_t"
  where
    "wcode_on_checking_3 ires rs (l, r) = 
         (\<exists> ln rn. l = Bk # ires \<and>
             r = Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

fun wcode_goon_checking_3 :: "bin_inv_t"
  where
    "wcode_goon_checking_3 ires rs (l, r) = 
         (\<exists> ln rn. l = ires \<and>
             r = Bk # Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

fun wcode_stop :: "bin_inv_t"
  where
    "wcode_stop ires rs (l, r) = 
          (\<exists> ln rn. l = Bk # ires \<and>
             r = Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

fun wcode_halt_case_inv :: "nat \<Rightarrow> bin_inv_t"
  where
    "wcode_halt_case_inv st ires rs (l, r) = 
          (if st = 0 then wcode_stop ires rs (l, r)
           else if st = Suc 0 then wcode_on_left_moving_3 ires rs (l, r)
           else if st = Suc (Suc 0) then wcode_on_checking_3 ires rs (l, r)
           else if st = 7 then wcode_goon_checking_3 ires rs (l, r)
           else False)"

fun wcode_halt_case_state :: "config \<Rightarrow> nat"
  where
    "wcode_halt_case_state (st, l, r) = 
           (if st = 1 then 5
            else if st = Suc (Suc 0) then 4
            else if st = 7 then 3
            else 0)"

fun wcode_halt_case_step :: "config \<Rightarrow> nat"
  where
    "wcode_halt_case_step (st, l, r) = 
         (if st = 1 then length l
         else 0)"

fun wcode_halt_case_measure :: "config \<Rightarrow> nat \<times> nat"
  where
    "wcode_halt_case_measure (st, l, r) = 
     (wcode_halt_case_state (st, l, r), 
      wcode_halt_case_step (st, l, r))"

definition wcode_halt_case_le :: "(config \<times> config) set"
  where "wcode_halt_case_le \<equiv> (inv_image lex_pair wcode_halt_case_measure)"

lemma wf_wcode_halt_case_le[intro]: "wf wcode_halt_case_le"
  by(auto simp: wcode_halt_case_le_def)

declare wcode_on_left_moving_3_B.simps[simp del] wcode_on_left_moving_3_O.simps[simp del]  
  wcode_on_checking_3.simps[simp del] wcode_goon_checking_3.simps[simp del] 
  wcode_on_left_moving_3.simps[simp del] wcode_stop.simps[simp del]

lemmas wcode_halt_invs = 
  wcode_on_left_moving_3_B.simps wcode_on_left_moving_3_O.simps
  wcode_on_checking_3.simps wcode_goon_checking_3.simps 
  wcode_on_left_moving_3.simps wcode_stop.simps


lemma wcode_on_left_moving_3_mv_Bk[simp]: "wcode_on_left_moving_3 ires rs (b, Bk # list)
 \<Longrightarrow> wcode_on_left_moving_3 ires rs (tl b, hd b # Bk # list)"
  apply(simp only: wcode_halt_invs)
  apply(erule_tac disjE)
   apply(erule_tac exE)+ apply(rename_tac ml mr rn)
   apply(case_tac ml, simp)
    apply(rule_tac x = "mr - 2" in exI, rule_tac x = rn in exI)
    apply(case_tac mr, force, simp add: exp_ind del: replicate_Suc)
    apply(case_tac "mr - 1", force, simp add: exp_ind del: replicate_Suc)
   apply force
  apply force
  done

lemma wcode_goon_checking_3_cases[simp]: "wcode_goon_checking_3 ires rs (b, Bk # list) \<Longrightarrow> 
  (b = [] \<longrightarrow> wcode_stop ires rs ([Bk], list)) \<and>
  (b \<noteq> [] \<longrightarrow> wcode_stop ires rs (Bk # b, list))"
  apply(auto simp: wcode_halt_invs)
  done

lemma wcode_on_checking_3_mv_Oc[simp]: "wcode_on_left_moving_3 ires rs (b, Oc # list) \<Longrightarrow> 
               wcode_on_checking_3 ires rs (tl b, hd b # Oc # list)"
  by(simp add:wcode_halt_invs)

lemma wcode_3_nonempty[simp]:
  "wcode_on_left_moving_3 ires rs (b, []) = False"
  "wcode_on_checking_3 ires rs (b, []) = False"
  "wcode_goon_checking_3 ires rs (b, []) = False"
  "wcode_on_left_moving_3 ires rs (b, Oc # list) \<Longrightarrow> b \<noteq> []"
  "wcode_on_checking_3 ires rs (b, Oc # list) = False"
  "wcode_on_left_moving_3 ires rs (b, Bk # list) \<Longrightarrow> b \<noteq> []"
  "wcode_on_checking_3 ires rs (b, Bk # list) \<Longrightarrow> b \<noteq> []"
  "wcode_goon_checking_3 ires rs (b, Oc # list) = False"
  by(auto simp: wcode_halt_invs)

lemma wcode_goon_checking_3_mv_Bk[simp]: "wcode_on_checking_3 ires rs (b, Bk # list) \<Longrightarrow> 
  wcode_goon_checking_3 ires rs (tl b, hd b # Bk # list)"
  apply(auto simp: wcode_halt_invs)
  done

lemma t_halt_case_correctness: 
  shows "let P = (\<lambda> (st, l, r). st = 0) in 
       let Q = (\<lambda> (st, l, r). wcode_halt_case_inv st ires rs (l, r)) in 
       let f = (\<lambda> stp. steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # Bk # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp) in
       \<exists> n .P (f n) \<and> Q (f (n::nat))"
proof -
  let ?P = "(\<lambda> (st, l, r). st = 0)"
  let ?Q = "(\<lambda> (st, l, r). wcode_halt_case_inv st ires rs (l, r))"
  let ?f = "(\<lambda> stp. steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # Bk # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp)"
  have "\<exists> n. ?P (?f n) \<and> ?Q (?f (n::nat))"
  proof(rule_tac halt_lemma2)
    show "wf wcode_halt_case_le" by auto
  next
    { fix na
      obtain a b c where abc:"?f na = (a,b,c)" by(cases "?f na",auto)
      hence "\<not> ?P (?f na) \<and> ?Q (?f na) \<Longrightarrow>
                    ?Q (?f (Suc na)) \<and> (?f (Suc na), ?f na) \<in> wcode_halt_case_le"
        apply(simp add: step.simps)
        apply(cases c;cases "hd c")
           apply(auto simp: wcode_halt_case_le_def lex_pair_def split: if_splits)
        done
    }
    thus "\<forall> na. \<not> ?P (?f na) \<and> ?Q (?f na) \<longrightarrow> 
                    ?Q (?f (Suc na)) \<and> (?f (Suc na), ?f na) \<in> wcode_halt_case_le" by blast     
  next 
    show "?Q (?f 0)"
      apply(simp add: steps.simps wcode_halt_invs)
      apply(rule_tac x = "Suc m" in exI, simp)
      apply(rule_tac x = "Suc 0" in exI, auto)
      done
  next
    show "\<not> ?P (?f 0)"
      apply(simp add: steps.simps)
      done
  qed
  thus "?thesis"
    apply(auto)
    done
qed

declare wcode_halt_case_inv.simps[simp del]
lemma leading_Oc[intro]: "\<exists> xs. (<rev list @ [aa::nat]> :: cell list) = Oc # xs"
  apply(case_tac "rev list", simp)
  apply(simp add: tape_of_nl_cons)
  done

lemma wcode_halt_case:
  "\<exists>stp ln rn. steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # Bk # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n))
  t_wcode_main stp  = (0, Bk # ires, Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"
proof -
  let ?P = "\<lambda>(st, l, r). st = 0"
  let ?Q = "\<lambda>(st, l, r). wcode_halt_case_inv st ires rs (l, r)"
  let ?f = "steps0 (Suc 0, Bk # Bk \<up> m @ Oc # Bk # Bk # ires, Bk # Oc \<up> Suc rs @ Bk \<up> n) t_wcode_main"
  from t_halt_case_correctness[of ires rs m n] obtain n where "?P (?f n) \<and> ?Q (?f n)" by metis
  thus ?thesis
    apply(simp add: wcode_halt_case_inv.simps wcode_stop.simps)
    apply(case_tac "steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # Bk # ires,
                Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main n")
    apply(auto simp: wcode_halt_case_inv.simps wcode_stop.simps)
    by auto
qed

lemma bl_bin_one[simp]: "bl_bin [Oc] = 1"
  apply(simp add: bl_bin.simps)
  done

lemma twice_power[intro]: "2 * 2 ^ a = Suc (Suc (2 * bl_bin (Oc \<up> a)))"
  apply(induct a, auto simp: bl_bin.simps)
  done
declare replicate_Suc[simp del]

lemma t_wcode_main_lemma_pre:
  "\<lbrakk>args \<noteq> []; lm = <args::nat list>\<rbrakk> \<Longrightarrow> 
       \<exists> stp ln rn. steps0 (Suc 0, Bk # Bk\<up>(m) @ rev lm @ Bk # Bk # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main
                    stp
      = (0, Bk # ires, Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(bl_bin lm + rs * 2^(length lm - 1) ) @ Bk\<up>(rn))"
proof(induct "length args" arbitrary: args lm rs m n, simp)
  fix x args lm rs m n
  assume ind:
    "\<And>args lm rs m n.
    \<lbrakk>x = length args; (args::nat list) \<noteq> []; lm = <args>\<rbrakk>
    \<Longrightarrow> \<exists>stp ln rn.
    steps0 (Suc 0, Bk # Bk\<up>(m) @ rev lm @ Bk # Bk # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
    (0, Bk # ires, Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(bl_bin lm + rs * 2 ^ (length lm - 1)) @ Bk\<up>(rn))"
    and h: "Suc x = length args" "(args::nat list) \<noteq> []" "lm = <args>"
  from h have "\<exists> (a::nat) xs. args = xs @ [a]"
    apply(rule_tac x = "last args" in exI)
    apply(rule_tac x = "butlast args" in exI, auto)
    done    
  from this obtain a xs where "args = xs @ [a]" by blast
  from h and this show
    "\<exists>stp ln rn.
    steps0 (Suc 0, Bk # Bk\<up>(m) @ rev lm @ Bk # Bk # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
    (0, Bk # ires, Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(bl_bin lm + rs * 2 ^ (length lm - 1)) @ Bk\<up>(rn))"
  proof(case_tac "xs::nat list", simp)
    show "\<exists>stp ln rn.
          steps0 (Suc 0, Bk # Bk \<up> m @ Oc \<up> Suc a @ Bk # Bk # ires, Bk # Oc \<up> Suc rs @ Bk \<up> n) t_wcode_main stp =
          (0, Bk # ires, Bk # Oc # Bk \<up> ln @ Bk # Bk # Oc \<up> (bl_bin (Oc \<up> Suc a) + rs * 2 ^ a) @ Bk \<up> rn)"
    proof(induct "a" arbitrary: m n rs ires, simp)
      fix m n rs ires
      show "\<exists>stp ln rn.
          steps0 (Suc 0, Bk # Bk \<up> m @ Oc # Bk # Bk # ires, Bk # Oc \<up> Suc rs @ Bk \<up> n) t_wcode_main stp =
          (0, Bk # ires, Bk # Oc # Bk \<up> ln @ Bk # Bk # Oc \<up> Suc rs @ Bk \<up> rn)"
        apply(rule_tac wcode_halt_case)
        done
    next
      fix a m n rs ires
      assume ind2:
        "\<And>m n rs ires.
           \<exists>stp ln rn.
              steps0 (Suc 0, Bk # Bk \<up> m @ Oc \<up> Suc a @ Bk # Bk # ires, Bk # Oc \<up> Suc rs @ Bk \<up> n) t_wcode_main stp =
              (0, Bk # ires, Bk # Oc # Bk \<up> ln @ Bk # Bk # Oc \<up> (bl_bin (Oc \<up> Suc a) + rs * 2 ^ a) @ Bk \<up> rn)"
      show " \<exists>stp ln rn.
          steps0 (Suc 0, Bk # Bk \<up> m @ Oc \<up> Suc (Suc a) @ Bk # Bk # ires, Bk # Oc \<up> Suc rs @ Bk \<up> n) t_wcode_main stp =
          (0, Bk # ires, Bk # Oc # Bk \<up> ln @ Bk # Bk # Oc \<up> (bl_bin (Oc \<up> Suc (Suc a)) + rs * 2 ^ Suc a) @ Bk \<up> rn)"
      proof -
        have "\<exists>stp ln rn.
          steps0 (Suc 0, Bk # Bk\<up>(m) @ rev (<Suc a>) @ Bk # Bk # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
          (Suc 0, Bk # Bk\<up>(ln) @ rev (<a>) @ Bk # Bk # ires, Bk # Oc\<up>(Suc (2 * rs + 2)) @ Bk\<up>(rn))"
          apply(simp add: tape_of_nat)
          using wcode_double_case[of m "Oc\<up>(a) @ Bk # Bk # ires" rs n]
          apply(simp add: replicate_Suc)
          done
        from this obtain stpa lna rna where stp1:  
          "steps0 (Suc 0, Bk # Bk\<up>(m) @ rev (<Suc a>) @ Bk # Bk # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stpa =
          (Suc 0, Bk # Bk\<up>(lna) @ rev (<a>) @ Bk # Bk # ires, Bk # Oc\<up>(Suc (2 * rs + 2)) @ Bk\<up>(rna))" by blast
        moreover have 
          "\<exists>stp ln rn.
          steps0 (Suc 0,  Bk # Bk\<up>(lna) @ rev (<a::nat>) @ Bk # Bk # ires, Bk # Oc\<up>(Suc (2 * rs + 2)) @ Bk\<up>(rna)) t_wcode_main stp =
          (0, Bk # ires, Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(bl_bin (<a>) + (2*rs + 2)  * 2 ^ a) @ Bk\<up>(rn))"
          using ind2[of lna ires "2*rs + 2" rna] by(simp add: tape_of_list_def tape_of_nat_def)   
        from this obtain stpb lnb rnb where stp2:  
          "steps0 (Suc 0,  Bk # Bk\<up>(lna) @ rev (<a>) @ Bk # Bk # ires, Bk # Oc\<up>(Suc (2 * rs + 2)) @ Bk\<up>(rna)) t_wcode_main stpb =
          (0, Bk # ires, Bk # Oc # Bk\<up>(lnb) @ Bk # Bk # Oc\<up>(bl_bin (<a>) + (2*rs + 2)  * 2 ^ a) @ Bk\<up>(rnb))"
          by blast
        from stp1 and stp2 show "?thesis"
          apply(rule_tac x = "stpa + stpb" in exI,
              rule_tac x = lnb in exI, rule_tac x = rnb in exI, simp add: tape_of_nat_def)
          apply(simp add:  bl_bin.simps replicate_Suc)
          apply(auto)
          done
      qed
    qed
  next
    fix aa list
    assume g: "Suc x = length args" "args \<noteq> []" "lm = <args>" "args = xs @ [a::nat]" "xs = (aa::nat) # list"
    thus "\<exists>stp ln rn. steps0 (Suc 0, Bk # Bk\<up>(m) @ rev lm @ Bk # Bk # ires, Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
      (0, Bk # ires, Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(bl_bin lm + rs * 2 ^ (length lm - 1)) @ Bk\<up>(rn))"
    proof(induct a arbitrary: m n rs args lm, simp_all add: tape_of_nl_rev, 
        simp only: tape_of_nl_cons_app1, simp)
      fix m n rs args lm
      have "\<exists>stp ln rn.
        steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # rev (<(aa::nat) # list>) @ Bk # Bk # ires,
        Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
        (Suc 0, Bk # Bk\<up>(ln) @ rev (<aa # list>) @ Bk # Bk # ires, 
        Bk # Oc\<up>(Suc (4*rs + 4)) @ Bk\<up>(rn))"
      proof(simp add: tape_of_nl_rev)
        have "\<exists> xs. (<rev list @ [aa]>) = Oc # xs" by auto           
        from this obtain xs where "(<rev list @ [aa]>) = Oc # xs" ..
        thus "\<exists>stp ln rn.
            steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # <rev list @ [aa]> @ Bk # Bk # ires,
            Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
            (Suc 0, Bk # Bk\<up>(ln) @ <rev list @ [aa]> @ Bk # Bk # ires, Bk # Oc\<up>(5 + 4 * rs) @ Bk\<up>(rn))"
          apply(simp)
          using wcode_fourtimes_case[of m "xs @ Bk # Bk # ires" rs n]
          apply(simp)
          done
      qed
      from this obtain stpa lna rna where stp1:
        "steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # rev (<aa # list>) @ Bk # Bk # ires,
        Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stpa =
        (Suc 0, Bk # Bk\<up>(lna) @ rev (<aa # list>) @ Bk # Bk # ires, 
        Bk # Oc\<up>(Suc (4*rs + 4)) @ Bk\<up>(rna))" by blast
      from g have 
        "\<exists> stp ln rn. steps0 (Suc 0, Bk # Bk\<up>(lna) @ rev (<(aa::nat) # list>) @ Bk # Bk # ires, 
        Bk # Oc\<up>(Suc (4*rs + 4)) @ Bk\<up>(rna)) t_wcode_main stp = (0, Bk # ires, 
        Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(bl_bin (<aa#list>)+ (4*rs + 4) * 2^(length (<aa#list>) - 1) ) @ Bk\<up>(rn))"
        apply(rule_tac args = "(aa::nat)#list" in ind, simp_all)
        done
      from this obtain stpb lnb rnb where stp2:
        "steps0 (Suc 0, Bk # Bk\<up>(lna) @ rev (<(aa::nat) # list>) @ Bk # Bk # ires, 
         Bk # Oc\<up>(Suc (4*rs + 4)) @ Bk\<up>(rna)) t_wcode_main stpb = (0, Bk # ires, 
         Bk # Oc # Bk\<up>(lnb) @ Bk # Bk # Oc\<up>(bl_bin (<aa#list>)+ (4*rs + 4) * 2^(length (<aa#list>) - 1) ) @ Bk\<up>(rnb))"
        by blast
      from stp1 and stp2 and h
      show "\<exists>stp ln rn.
         steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc # Bk # <rev list @ [aa]> @ Bk # Bk # ires,
         Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
         (0, Bk # ires, Bk # Oc # Bk\<up>(ln) @ Bk #
         Bk # Oc\<up>(bl_bin (Oc\<up>(Suc aa) @ Bk # <list @ [0]>) + rs * (2 * 2 ^ (aa + length (<list @ [0]>)))) @ Bk\<up>(rn))"
        apply(rule_tac x = "stpa + stpb" in exI, rule_tac x = lnb in exI,
            rule_tac x = rnb in exI, simp add: steps_add tape_of_nl_rev)
        done
    next
      fix ab m n rs args lm
      assume ind2:
        "\<And> m n rs args lm.
         \<lbrakk>lm = <aa # list @ [ab]>; args = aa # list @ [ab]\<rbrakk>
         \<Longrightarrow> \<exists>stp ln rn.
         steps0 (Suc 0, Bk # Bk\<up>(m) @ <ab # rev list @ [aa]> @ Bk # Bk # ires,
         Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
         (0, Bk # ires, Bk # Oc # Bk\<up>(ln) @ Bk #
         Bk # Oc\<up>(bl_bin (<aa # list @ [ab]>) + rs * 2 ^ (length (<aa # list @ [ab]>) - Suc 0)) @ Bk\<up>(rn))"
        and k: "args = aa # list @ [Suc ab]" "lm = <aa # list @ [Suc ab]>"
      show "\<exists>stp ln rn.
         steps0 (Suc 0, Bk # Bk\<up>(m) @ <Suc ab # rev list @ [aa]> @ Bk # Bk # ires,
         Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
         (0, Bk # ires,Bk # Oc # Bk\<up>(ln) @ Bk # 
         Bk # Oc\<up>(bl_bin (<aa # list @ [Suc ab]>) + rs * 2 ^ (length (<aa # list @ [Suc ab]>) - Suc 0)) @ Bk\<up>(rn))"
      proof(simp add: tape_of_nl_cons_app1)
        have "\<exists>stp ln rn.
           steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc\<up>(Suc (Suc ab)) @ Bk # <rev list @ [aa]> @ Bk # Bk # ires, 
           Bk # Oc # Oc\<up>(rs) @ Bk\<up>(n)) t_wcode_main stp
           = (Suc 0, Bk # Bk\<up>(ln) @ Oc\<up>(Suc ab) @ Bk # <rev list @ [aa]> @ Bk # Bk # ires,
           Bk # Oc\<up>(Suc (2*rs + 2)) @ Bk\<up>(rn))"
          using wcode_double_case[of m "Oc\<up>(ab) @ Bk # <rev list @ [aa]> @ Bk # Bk # ires"
              rs n]
          apply(simp add: replicate_Suc)
          done
        from this obtain stpa lna rna where stp1:
          "steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc\<up>(Suc (Suc ab)) @ Bk # <rev list @ [aa]> @ Bk # Bk # ires, 
           Bk # Oc # Oc\<up>(rs) @ Bk\<up>(n)) t_wcode_main stpa
           = (Suc 0, Bk # Bk\<up>(lna) @ Oc\<up>(Suc ab) @ Bk # <rev list @ [aa]> @ Bk # Bk # ires,
           Bk # Oc\<up>(Suc (2*rs + 2)) @ Bk\<up>(rna))" by blast
        from k have 
          "\<exists> stp ln rn. steps0 (Suc 0, Bk # Bk\<up>(lna) @ <ab # rev list @ [aa]> @ Bk # Bk # ires,
           Bk # Oc\<up>(Suc (2*rs + 2)) @ Bk\<up>(rna)) t_wcode_main stp
           = (0, Bk # ires, Bk # Oc # Bk\<up>(ln) @ Bk #
           Bk # Oc\<up>(bl_bin (<aa # list @ [ab]> ) +  (2*rs + 2)* 2^(length (<aa # list @ [ab]>) - Suc 0)) @ Bk\<up>(rn))"
          apply(rule_tac ind2, simp_all)
          done
        from this obtain stpb lnb rnb where stp2: 
          "steps0 (Suc 0, Bk # Bk\<up>(lna) @  <ab # rev list @ [aa]> @ Bk # Bk # ires,
           Bk # Oc\<up>(Suc (2*rs + 2)) @ Bk\<up>(rna)) t_wcode_main stpb
           = (0, Bk # ires, Bk # Oc # Bk\<up>(lnb) @ Bk #
           Bk # Oc\<up>(bl_bin (<aa # list @ [ab]> ) +  (2*rs + 2)* 2^(length (<aa # list @ [ab]>) - Suc 0)) @ Bk\<up>(rnb))" 
          by blast
        from stp1 and stp2 show 
          "\<exists>stp ln rn.
           steps0 (Suc 0, Bk # Bk\<up>(m) @ Oc\<up>(Suc (Suc ab)) @ Bk # <rev list @ [aa]> @ Bk # Bk # ires,
           Bk # Oc\<up>(Suc rs) @ Bk\<up>(n)) t_wcode_main stp =
           (0, Bk # ires, Bk # Oc # Bk\<up>(ln) @ Bk # Bk # 
           Oc\<up>(bl_bin (Oc\<up>(Suc aa) @ Bk # <list @ [Suc ab]>) + rs * (2 * 2 ^ (aa + length (<list @ [Suc ab]>)))) 
           @ Bk\<up>(rn))"
          apply(rule_tac x = "stpa + stpb" in exI, rule_tac x = lnb in exI,
              rule_tac x = rnb in exI, simp add: steps_add tape_of_nl_cons_app1 replicate_Suc)
          done
      qed
    qed
  qed
qed


definition t_wcode_prepare :: "instr list"
  where
    "t_wcode_prepare \<equiv> 
         [(W1, 2), (L, 1), (L, 3), (R, 2), (R, 4), (W0, 3),
          (R, 4), (R, 5), (R, 6), (R, 5), (R, 7), (R, 5),
          (W1, 7), (L, 0)]"

fun wprepare_add_one :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_add_one m lm (l, r) = 
      (\<exists> rn. l = [] \<and>
               (r = <m # lm> @ Bk\<up>(rn) \<or> 
                r = Bk # <m # lm> @ Bk\<up>(rn)))"

fun wprepare_goto_first_end :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_goto_first_end m lm (l, r) = 
      (\<exists> ml mr rn. l = Oc\<up>(ml) \<and>
                      r = Oc\<up>(mr) @ Bk # <lm> @ Bk\<up>(rn) \<and>
                      ml + mr = Suc (Suc m))"

fun wprepare_erase :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow>  bool"
  where
    "wprepare_erase m lm (l, r) = 
     (\<exists> rn. l = Oc\<up>(Suc m) \<and> 
               tl r = Bk # <lm> @ Bk\<up>(rn))"

fun wprepare_goto_start_pos_B :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_goto_start_pos_B m lm (l, r) = 
     (\<exists> rn. l = Bk # Oc\<up>(Suc m) \<and>
               r = Bk # <lm> @ Bk\<up>(rn))"

fun wprepare_goto_start_pos_O :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_goto_start_pos_O m lm (l, r) = 
     (\<exists> rn. l = Bk # Bk # Oc\<up>(Suc m) \<and>
               r = <lm> @ Bk\<up>(rn))"

fun wprepare_goto_start_pos :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_goto_start_pos m lm (l, r) = 
       (wprepare_goto_start_pos_B m lm (l, r) \<or>
        wprepare_goto_start_pos_O m lm (l, r))"

fun wprepare_loop_start_on_rightmost :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_loop_start_on_rightmost m lm (l, r) = 
     (\<exists> rn mr. rev l @ r = Oc\<up>(Suc m) @ Bk # Bk # <lm> @ Bk\<up>(rn) \<and> l \<noteq> [] \<and>
                       r = Oc\<up>(mr) @ Bk\<up>(rn))"

fun wprepare_loop_start_in_middle :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_loop_start_in_middle m lm (l, r) =
     (\<exists> rn (mr:: nat) (lm1::nat list). 
  rev l @ r = Oc\<up>(Suc m) @ Bk # Bk # <lm> @ Bk\<up>(rn) \<and> l \<noteq> [] \<and>
  r = Oc\<up>(mr) @ Bk # <lm1> @ Bk\<up>(rn) \<and> lm1 \<noteq> [])"

fun wprepare_loop_start :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_loop_start m lm (l, r) = (wprepare_loop_start_on_rightmost m lm (l, r) \<or> 
                                      wprepare_loop_start_in_middle m lm (l, r))"

fun wprepare_loop_goon_on_rightmost :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_loop_goon_on_rightmost m lm (l, r) = 
     (\<exists> rn. l = Bk # <rev lm> @ Bk # Bk # Oc\<up>(Suc m) \<and>
               r = Bk\<up>(rn))"

fun wprepare_loop_goon_in_middle :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_loop_goon_in_middle m lm (l, r) = 
     (\<exists> rn (mr:: nat) (lm1::nat list). 
  rev l @ r = Oc\<up>(Suc m) @ Bk # Bk # <lm> @ Bk\<up>(rn) \<and> l \<noteq> [] \<and>
                     (if lm1 = [] then r = Oc\<up>(mr) @ Bk\<up>(rn) 
                     else r = Oc\<up>(mr) @ Bk # <lm1> @ Bk\<up>(rn)) \<and> mr > 0)"

fun wprepare_loop_goon :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_loop_goon m lm (l, r) = 
              (wprepare_loop_goon_in_middle m lm (l, r) \<or> 
               wprepare_loop_goon_on_rightmost m lm (l, r))"

fun wprepare_add_one2 :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_add_one2 m lm (l, r) =
          (\<exists> rn. l = Bk # Bk # <rev lm> @ Bk # Bk # Oc\<up>(Suc m) \<and>
               (r = [] \<or> tl r = Bk\<up>(rn)))"

fun wprepare_stop :: "nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_stop m lm (l, r) = 
         (\<exists> rn. l = Bk # <rev lm> @ Bk # Bk # Oc\<up>(Suc m) \<and>
               r = Bk # Oc # Bk\<up>(rn))"

fun wprepare_inv :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wprepare_inv st m lm (l, r) = 
        (if st = 0 then wprepare_stop m lm (l, r) 
         else if st = Suc 0 then wprepare_add_one m lm (l, r)
         else if st = Suc (Suc 0) then wprepare_goto_first_end m lm (l, r)
         else if st = Suc (Suc (Suc 0)) then wprepare_erase m lm (l, r)
         else if st = 4 then wprepare_goto_start_pos m lm (l, r)
         else if st = 5 then wprepare_loop_start m lm (l, r)
         else if st = 6 then wprepare_loop_goon m lm (l, r)
         else if st = 7 then wprepare_add_one2 m lm (l, r)
         else False)"

fun wprepare_stage :: "config \<Rightarrow> nat"
  where
    "wprepare_stage (st, l, r) = 
      (if st \<ge> 1 \<and> st \<le> 4 then 3
       else if st = 5 \<or> st = 6 then 2
       else 1)"

fun wprepare_state :: "config \<Rightarrow> nat"
  where
    "wprepare_state (st, l, r) = 
       (if st = 1 then 4
        else if st = Suc (Suc 0) then 3
        else if st = Suc (Suc (Suc 0)) then 2
        else if st = 4 then 1
        else if st = 7 then 2
        else 0)"

fun wprepare_step :: "config \<Rightarrow> nat"
  where
    "wprepare_step (st, l, r) = 
      (if st = 1 then (if hd r = Oc then Suc (length l)
                       else 0)
       else if st = Suc (Suc 0) then length r
       else if st = Suc (Suc (Suc 0)) then (if hd r = Oc then 1
                            else 0)
       else if st = 4 then length r
       else if st = 5 then Suc (length r)
       else if st = 6 then (if r = [] then 0 else Suc (length r))
       else if st = 7 then (if (r \<noteq> [] \<and> hd r = Oc) then 0
                            else 1)
       else 0)"

fun wcode_prepare_measure :: "config \<Rightarrow> nat \<times> nat \<times> nat"
  where
    "wcode_prepare_measure (st, l, r) = 
     (wprepare_stage (st, l, r), 
      wprepare_state (st, l, r), 
      wprepare_step (st, l, r))"

definition wcode_prepare_le :: "(config \<times> config) set"
  where "wcode_prepare_le \<equiv> (inv_image lex_triple wcode_prepare_measure)"

lemma wf_wcode_prepare_le[intro]: "wf wcode_prepare_le"
  by(auto intro:wf_inv_image simp: wcode_prepare_le_def 
      lex_triple_def)

declare wprepare_add_one.simps[simp del] wprepare_goto_first_end.simps[simp del]
  wprepare_erase.simps[simp del] wprepare_goto_start_pos.simps[simp del]
  wprepare_loop_start.simps[simp del] wprepare_loop_goon.simps[simp del]
  wprepare_add_one2.simps[simp del]

lemmas wprepare_invs = wprepare_add_one.simps wprepare_goto_first_end.simps
  wprepare_erase.simps wprepare_goto_start_pos.simps
  wprepare_loop_start.simps wprepare_loop_goon.simps
  wprepare_add_one2.simps

declare wprepare_inv.simps[simp del]

lemma fetch_t_wcode_prepare[simp]:
  "fetch t_wcode_prepare (Suc 0) Bk = (W1, 2)"
  "fetch t_wcode_prepare (Suc 0) Oc = (L, 1)"
  "fetch t_wcode_prepare (Suc (Suc 0)) Bk = (L, 3)"
  "fetch t_wcode_prepare (Suc (Suc 0)) Oc = (R, 2)"
  "fetch t_wcode_prepare (Suc (Suc (Suc 0))) Bk = (R, 4)"
  "fetch t_wcode_prepare (Suc (Suc (Suc 0))) Oc = (W0, 3)"
  "fetch t_wcode_prepare 4 Bk = (R, 4)"
  "fetch t_wcode_prepare 4 Oc = (R, 5)"
  "fetch t_wcode_prepare 5 Oc = (R, 5)"
  "fetch t_wcode_prepare 5 Bk = (R, 6)"
  "fetch t_wcode_prepare 6 Oc = (R, 5)"
  "fetch t_wcode_prepare 6 Bk = (R, 7)"
  "fetch t_wcode_prepare 7 Oc = (L, 0)"
  "fetch t_wcode_prepare 7 Bk = (W1, 7)"
  unfolding fetch.simps t_wcode_prepare_def nth_of.simps
    numeral by auto

lemma wprepare_add_one_nonempty_snd[simp]: "lm \<noteq> [] \<Longrightarrow> wprepare_add_one m lm (b, []) = False"
  apply(simp add: wprepare_invs)
  done

lemma wprepare_goto_first_end_nonempty_snd[simp]: "lm \<noteq> [] \<Longrightarrow> wprepare_goto_first_end m lm (b, []) = False"
  apply(simp add: wprepare_invs)
  done

lemma wprepare_erase_nonempty_snd[simp]: "lm \<noteq> [] \<Longrightarrow> wprepare_erase m lm (b, []) = False"
  apply(simp add: wprepare_invs)
  done

lemma wprepare_goto_start_pos_nonempty_snd[simp]: "lm \<noteq> [] \<Longrightarrow> wprepare_goto_start_pos m lm (b, []) = False"
  apply(simp add: wprepare_invs)
  done

lemma wprepare_loop_start_empty_nonempty_fst[simp]: "\<lbrakk>lm \<noteq> []; wprepare_loop_start m lm (b, [])\<rbrakk> \<Longrightarrow> b \<noteq> []"
  apply(simp add: wprepare_invs)
  done

lemma rev_eq: "rev xs = rev ys \<Longrightarrow> xs = ys" by auto

lemma wprepare_loop_goon_Bk_empty_snd[simp]: "\<lbrakk>lm \<noteq> []; wprepare_loop_start m lm (b, [])\<rbrakk> \<Longrightarrow> 
                                  wprepare_loop_goon m lm (Bk # b, [])"
  apply(simp only: wprepare_invs)
  apply(erule_tac disjE)
   apply(rule_tac disjI2)
   apply(simp add: wprepare_loop_start_on_rightmost.simps
      wprepare_loop_goon_on_rightmost.simps, auto)
  apply(rule_tac rev_eq, simp add: tape_of_nl_rev)
  done

lemma wprepare_loop_goon_nonempty_fst[simp]: "\<lbrakk>lm \<noteq> []; wprepare_loop_goon m lm (b, [])\<rbrakk> \<Longrightarrow> b \<noteq> []"
  apply(simp only: wprepare_invs, auto)
  done

lemma wprepare_add_one2_Bk_empty[simp]:"\<lbrakk>lm \<noteq> []; wprepare_loop_goon m lm (b, [])\<rbrakk> \<Longrightarrow> 
  wprepare_add_one2 m lm (Bk # b, [])"
  apply(simp only: wprepare_invs, auto split: if_splits)
  done

lemma wprepare_add_one2_nonempty_fst[simp]: "wprepare_add_one2 m lm (b, []) \<Longrightarrow> b \<noteq> []"
  apply(simp only: wprepare_invs, auto)
  done

lemma wprepare_add_one2_Oc[simp]: "wprepare_add_one2 m lm (b, []) \<Longrightarrow> wprepare_add_one2 m lm (b, [Oc])"
  apply(simp only: wprepare_invs, auto)
  done

lemma Bk_not_tape_start[simp]: "(Bk # list = <(m::nat) # lm> @ ys) = False"
  apply(case_tac lm, auto simp: tape_of_nl_cons replicate_Suc)
  done

lemma wprepare_goto_first_end_cases[simp]:
  "\<lbrakk>lm \<noteq> []; wprepare_add_one m lm (b, Bk # list)\<rbrakk>
       \<Longrightarrow> (b = [] \<longrightarrow> wprepare_goto_first_end m lm ([], Oc # list)) \<and> 
           (b \<noteq> [] \<longrightarrow> wprepare_goto_first_end m lm (b, Oc # list))"
  apply(simp only: wprepare_invs)
  apply(auto simp: tape_of_nl_cons split: if_splits)
  apply(cases lm, auto simp add:tape_of_list_def replicate_Suc)
  done

lemma wprepare_goto_first_end_Bk_nonempty_fst[simp]:
  "wprepare_goto_first_end m lm (b, Bk # list) \<Longrightarrow> b \<noteq> []"
  apply(simp only: wprepare_invs , auto simp: replicate_Suc)
  done

declare replicate_Suc[simp]

lemma wprepare_erase_elem_Bk_rest[simp]: "wprepare_goto_first_end m lm (b, Bk # list) \<Longrightarrow>
                          wprepare_erase m lm (tl b, hd b # Bk # list)"
  by(simp add: wprepare_invs)

lemma wprepare_erase_Bk_nonempty_fst[simp]: "wprepare_erase m lm (b, Bk # list) \<Longrightarrow> b \<noteq> []"
  by(simp add: wprepare_invs)

lemma wprepare_goto_start_pos_Bk[simp]: "wprepare_erase m lm (b, Bk # list) \<Longrightarrow> 
                           wprepare_goto_start_pos m lm (Bk # b, list)"
  apply(simp only: wprepare_invs, auto)
  done

lemma wprepare_add_one_Bk_nonempty_snd[simp]: "\<lbrakk>wprepare_add_one m lm (b, Bk # list)\<rbrakk> \<Longrightarrow> list \<noteq> []"
  apply(simp only: wprepare_invs)
  apply(case_tac lm, simp_all add: tape_of_list_def tape_of_nat_def, auto)
  done

lemma wprepare_goto_first_end_nonempty_snd_tl[simp]:
  "\<lbrakk>lm \<noteq> [];  wprepare_goto_first_end m lm (b, Bk # list)\<rbrakk> \<Longrightarrow> list \<noteq> []"
  by(simp only: wprepare_invs, auto)

lemma wprepare_erase_Bk_nonempty_list[simp]: "\<lbrakk>lm \<noteq> []; wprepare_erase m lm (b, Bk # list)\<rbrakk> \<Longrightarrow> list \<noteq> []"
  apply(simp only: wprepare_invs, auto)
  done


lemma wprepare_goto_start_pos_Bk_nonempty[simp]: "\<lbrakk>lm \<noteq> [];  wprepare_goto_start_pos m lm (b, Bk # list)\<rbrakk> \<Longrightarrow> list \<noteq> []"
  by(cases lm;cases list;simp only: wprepare_invs, auto)

lemma wprepare_goto_start_pos_Bk_nonempty_fst[simp]: "\<lbrakk>lm \<noteq> [];  wprepare_goto_start_pos m lm (b, Bk # list)\<rbrakk> \<Longrightarrow> b \<noteq> []"
  apply(simp only: wprepare_invs)
  apply(auto)
  done

lemma wprepare_loop_goon_Bk_nonempty[simp]: "\<lbrakk>lm \<noteq> []; wprepare_loop_goon m lm (b, Bk # list)\<rbrakk> \<Longrightarrow> b \<noteq> []"
  apply(simp only: wprepare_invs, auto)
  done

lemma wprepare_loop_goon_wprepare_add_one2_cases[simp]: "\<lbrakk>lm \<noteq> []; wprepare_loop_goon m lm (b, Bk # list)\<rbrakk> \<Longrightarrow> 
  (list = [] \<longrightarrow> wprepare_add_one2 m lm (Bk # b, [])) \<and> 
  (list \<noteq> [] \<longrightarrow> wprepare_add_one2 m lm (Bk # b, list))"
  unfolding wprepare_invs
  apply(cases list;auto split:nat.split if_splits)
  by (metis list.sel(3) tl_replicate)

lemma wprepare_add_one2_nonempty[simp]: "wprepare_add_one2 m lm (b, Bk # list) \<Longrightarrow> b \<noteq> []"
  apply(simp only: wprepare_invs, simp)
  done

lemma wprepare_add_one2_cases[simp]: "wprepare_add_one2 m lm (b, Bk # list) \<Longrightarrow> 
      (list = [] \<longrightarrow> wprepare_add_one2 m lm (b, [Oc])) \<and> 
      (list \<noteq> [] \<longrightarrow> wprepare_add_one2 m lm (b, Oc # list))"
  apply(simp only:  wprepare_invs, auto)
  done

lemma wprepare_goto_first_end_cases_Oc[simp]: "wprepare_goto_first_end m lm (b, Oc # list)
       \<Longrightarrow> (b = [] \<longrightarrow> wprepare_goto_first_end m lm ([Oc], list)) \<and> 
           (b \<noteq> [] \<longrightarrow> wprepare_goto_first_end m lm (Oc # b, list))"
  apply(simp only:  wprepare_invs, auto)
   apply(rule_tac x = 1 in exI, auto) apply(rename_tac ml mr rn)
  apply(case_tac mr, simp_all add: )
  apply(case_tac ml, simp_all add: )
  apply(rule_tac x = "Suc ml" in exI, simp_all add: )
  apply(rule_tac x = "mr - 1" in exI, simp)
  done

lemma wprepare_erase_nonempty[simp]: "wprepare_erase m lm (b, Oc # list) \<Longrightarrow> b \<noteq> []"
  apply(simp only: wprepare_invs, auto simp: )
  done

lemma wprepare_erase_Bk[simp]: "wprepare_erase m lm (b, Oc # list)
  \<Longrightarrow> wprepare_erase m lm (b, Bk # list)"
  apply(simp  only:wprepare_invs, auto simp: )
  done

lemma wprepare_goto_start_pos_Bk_move[simp]: "\<lbrakk>lm \<noteq> []; wprepare_goto_start_pos m lm (b, Bk # list)\<rbrakk>
       \<Longrightarrow> wprepare_goto_start_pos m lm (Bk # b, list)"
  apply(simp only:wprepare_invs, auto)
          apply(case_tac [!] lm, simp, simp_all)
  done

lemma wprepare_loop_start_b_nonempty[simp]: "wprepare_loop_start m lm (b, aa) \<Longrightarrow> b \<noteq> []"
  apply(simp only:wprepare_invs, auto)
  done
lemma exists_exp_of_Bk[elim]: "Bk # list = Oc\<up>(mr) @ Bk\<up>(rn)  \<Longrightarrow> \<exists>rn. list = Bk\<up>(rn)"
  apply(case_tac mr, simp_all)
  apply(case_tac rn, simp_all)
  done

lemma wprepare_loop_start_in_middle_Bk_False[simp]: "wprepare_loop_start_in_middle m lm (b, [Bk]) = False"
  by(auto)

declare wprepare_loop_start_in_middle.simps[simp del]

declare wprepare_loop_start_on_rightmost.simps[simp del] 
  wprepare_loop_goon_in_middle.simps[simp del]
  wprepare_loop_goon_on_rightmost.simps[simp del]

lemma wprepare_loop_goon_in_middle_Bk_False[simp]: "wprepare_loop_goon_in_middle m lm (Bk # b, []) = False"
  apply(simp add: wprepare_loop_goon_in_middle.simps, auto)
  done

lemma wprepare_loop_goon_Bk[simp]: "\<lbrakk>lm \<noteq> []; wprepare_loop_start m lm (b, [Bk])\<rbrakk> \<Longrightarrow>
  wprepare_loop_goon m lm (Bk # b, [])"
  unfolding wprepare_invs
  apply(auto simp add: wprepare_loop_goon_on_rightmost.simps 
      wprepare_loop_start_on_rightmost.simps)
  apply(rule_tac rev_eq)
  apply(simp add: tape_of_nl_rev)
  apply(simp add: exp_ind replicate_Suc[THEN sym] del: replicate_Suc)
  done

lemma wprepare_loop_goon_in_middle_Bk_False2[simp]: "wprepare_loop_start_on_rightmost m lm (b, Bk # a # lista)
 \<Longrightarrow> wprepare_loop_goon_in_middle m lm (Bk # b, a # lista) = False"
  apply(auto simp: wprepare_loop_start_on_rightmost.simps
      wprepare_loop_goon_in_middle.simps)
  done

lemma wprepare_loop_goon_on_rightbmost_Bk_False[simp]: "\<lbrakk>lm \<noteq> []; wprepare_loop_start_on_rightmost m lm (b, Bk # a # lista)\<rbrakk>
    \<Longrightarrow> wprepare_loop_goon_on_rightmost m lm (Bk # b, a # lista)"
  apply(simp only: wprepare_loop_start_on_rightmost.simps
      wprepare_loop_goon_on_rightmost.simps, auto simp: tape_of_nl_rev)
   apply(simp add: replicate_Suc[THEN sym] exp_ind tape_of_nl_rev del: replicate_Suc)
  by (meson Cons_replicate_eq)


lemma wprepare_loop_goon_in_middle_Bk_False3[simp]: 
  assumes "lm \<noteq> []" "wprepare_loop_start_in_middle m lm (b, Bk # a # lista)"
  shows "wprepare_loop_goon_in_middle m lm (Bk # b, a # lista)" (is "?t1")
    and "wprepare_loop_goon_on_rightmost m lm (Bk # b, a # lista) = False" (is ?t2)
proof -
  from assms obtain rn mr lm1 where *:"rev b @ Oc \<up> mr @ Bk # <lm1> = Oc # Oc \<up> m @ Bk # Bk # <lm>"
    "b \<noteq> []" "Bk # a # lista = Oc \<up> mr @ Bk # <lm1::nat list> @ Bk \<up> rn" "lm1 \<noteq> []"
    by(auto simp add: wprepare_loop_start_in_middle.simps)
  thus ?t1 apply(simp add: wprepare_loop_start_in_middle.simps
        wprepare_loop_goon_in_middle.simps, auto)
    apply(rule_tac x = rn in exI, simp)
    apply(case_tac mr, simp_all add: )
    apply(case_tac lm1, simp)
    apply(rule_tac x = "Suc (hd lm1)" in exI, simp)
    apply(rule_tac x = "tl lm1" in exI)
    apply(case_tac "tl lm1", simp_all add: tape_of_list_def  tape_of_nat_def)
    done
  from * show ?t2 
    apply(simp add: wprepare_loop_start_in_middle.simps
        wprepare_loop_goon_on_rightmost.simps del:split_head_repeat, auto simp del:split_head_repeat)
     apply(case_tac mr)
      apply(case_tac  "lm1::nat list", simp_all, case_tac "tl lm1", simp_all)
      apply(auto simp add: tape_of_list_def )
      apply(case_tac [!] rna, simp_all add: )
     apply(case_tac mr, simp_all add: )
     apply(case_tac lm1, simp, case_tac list, simp)
     apply(simp_all add: tape_of_nat_def)
    by (metis Bk_not_tape_start tape_of_list_def tape_of_nat_list.elims)
qed

lemma wprepare_loop_goon_Bk2[simp]: "\<lbrakk>lm \<noteq> []; wprepare_loop_start m lm (b, Bk # a # lista)\<rbrakk> \<Longrightarrow> 
  wprepare_loop_goon m lm (Bk # b, a # lista)"
  apply(simp add: wprepare_loop_start.simps 
      wprepare_loop_goon.simps)
  apply(erule_tac disjE, simp, auto)
  done

lemma start_2_goon:
  "\<lbrakk>lm \<noteq> []; wprepare_loop_start m lm (b, Bk # list)\<rbrakk> \<Longrightarrow>
   (list = [] \<longrightarrow> wprepare_loop_goon m lm (Bk # b, [])) \<and>
  (list \<noteq> [] \<longrightarrow> wprepare_loop_goon m lm (Bk # b, list))"
  apply(case_tac list, auto)
  done

lemma add_one_2_add_one: "wprepare_add_one m lm (b, Oc # list)
  \<Longrightarrow> (hd b = Oc \<longrightarrow> (b = [] \<longrightarrow> wprepare_add_one m lm ([], Bk # Oc # list)) \<and>
                     (b \<noteq> [] \<longrightarrow> wprepare_add_one m lm (tl b, Oc # Oc # list))) \<and>
  (hd b \<noteq> Oc \<longrightarrow> (b = [] \<longrightarrow> wprepare_add_one m lm ([], Bk # Oc # list)) \<and>
                 (b \<noteq> [] \<longrightarrow> wprepare_add_one m lm (tl b, hd b # Oc # list)))"
  unfolding wprepare_add_one.simps by auto

lemma wprepare_loop_start_on_rightmost_Oc[simp]: "wprepare_loop_start_on_rightmost m lm (b, Oc # list) \<Longrightarrow> 
  wprepare_loop_start_on_rightmost m lm (Oc # b, list)"
  apply(simp add: wprepare_loop_start_on_rightmost.simps)
  by (metis Cons_replicate_eq cell.distinct(1) list.sel(3) self_append_conv2 tl_append2 tl_replicate)

lemma wprepare_loop_start_in_middle_Oc[simp]:
  assumes "wprepare_loop_start_in_middle m lm (b, Oc # list)"
  shows "wprepare_loop_start_in_middle m lm (Oc # b, list)"
proof -
  from assms obtain mr lm1 rn
    where "rev b @ Oc \<up> mr @ Bk # <lm1::nat list> = Oc # Oc \<up> m @ Bk # Bk # <lm>"
      "Oc # list = Oc \<up> mr @ Bk # <lm1> @ Bk \<up> rn" "lm1 \<noteq> []"
    by(auto simp add: wprepare_loop_start_in_middle.simps)
  thus ?thesis 
    apply(auto simp add: wprepare_loop_start_in_middle.simps)
    apply(rule_tac x = rn in exI, auto)
    apply(case_tac mr, simp, simp add: )
    apply(rule_tac x = "mr - 1" in exI, simp)
    apply(rule_tac x = lm1 in exI, simp)
    done
qed

lemma start_2_start: "wprepare_loop_start m lm (b, Oc # list) \<Longrightarrow> 
       wprepare_loop_start m lm (Oc # b, list)"
  apply(simp add: wprepare_loop_start.simps)
  apply(erule_tac disjE, simp_all )
  done

lemma wprepare_loop_goon_Oc_nonempty[simp]: "wprepare_loop_goon m lm (b, Oc # list) \<Longrightarrow> b \<noteq> []"
  apply(simp add: wprepare_loop_goon.simps     
      wprepare_loop_goon_in_middle.simps 
      wprepare_loop_goon_on_rightmost.simps)
  apply(auto)
  done

lemma wprepare_goto_start_pos_Oc_nonempty[simp]: "wprepare_goto_start_pos m lm (b, Oc # list) \<Longrightarrow> b \<noteq> []"
  apply(simp add: wprepare_goto_start_pos.simps)
  done

lemma wprepare_loop_goon_on_rightmost_Oc_False[simp]: "wprepare_loop_goon_on_rightmost m lm (b, Oc # list) = False"
  apply(simp add: wprepare_loop_goon_on_rightmost.simps)
  done

lemma wprepare_loop1: "\<lbrakk>rev b @ Oc\<up>(mr) =  Oc\<up>(Suc m) @ Bk # Bk # <lm>; 
         b \<noteq> []; 0 < mr; Oc # list = Oc\<up>(mr) @ Bk\<up>(rn)\<rbrakk>
       \<Longrightarrow> wprepare_loop_start_on_rightmost m lm (Oc # b, list)"
  apply(simp add: wprepare_loop_start_on_rightmost.simps)
  apply(rule_tac x = rn in exI, simp)
  apply(case_tac mr, simp, simp)
  done

lemma wprepare_loop2: "\<lbrakk>rev b @ Oc\<up>(mr) @ Bk # <a # lista> = Oc\<up>(Suc m) @ Bk # Bk # <lm>;
                b \<noteq> []; Oc # list = Oc\<up>(mr) @ Bk # <(a::nat) # lista> @ Bk\<up>(rn)\<rbrakk>
       \<Longrightarrow>  wprepare_loop_start_in_middle m lm (Oc # b, list)"
  apply(simp add: wprepare_loop_start_in_middle.simps)
  apply(rule_tac x = rn in exI, simp)
  apply(case_tac mr, simp_all add: ) apply(rename_tac nat)
  apply(rule_tac x = nat in exI, simp)
  apply(rule_tac x = "a#lista" in exI, simp)
  done

lemma wprepare_loop_goon_in_middle_cases[simp]: "wprepare_loop_goon_in_middle m lm (b, Oc # list) \<Longrightarrow>
                wprepare_loop_start_on_rightmost m lm (Oc # b, list) \<or>
                wprepare_loop_start_in_middle m lm (Oc # b, list)"
  apply(simp add: wprepare_loop_goon_in_middle.simps split: if_splits) apply(rename_tac lm1)
  apply(case_tac lm1, simp_all add: wprepare_loop1 wprepare_loop2)
  done

lemma wprepare_add_one_b[simp]: "wprepare_add_one m lm (b, Oc # list)
       \<Longrightarrow> b = [] \<longrightarrow> wprepare_add_one m lm ([], Bk # Oc # list)"
  "wprepare_loop_goon m lm (b, Oc # list)
  \<Longrightarrow>  wprepare_loop_start m lm (Oc # b, list)"
   apply(auto simp add: wprepare_add_one.simps wprepare_loop_goon.simps
      wprepare_loop_start.simps)
  done

lemma wprepare_loop_start_on_rightmost_Oc2[simp]: "wprepare_goto_start_pos m [a] (b, Oc # list)
              \<Longrightarrow> wprepare_loop_start_on_rightmost m [a] (Oc # b, list) "
  apply(auto simp: wprepare_goto_start_pos.simps 
      wprepare_loop_start_on_rightmost.simps) apply(rename_tac rn)
  apply(rule_tac x = rn in exI, simp)
  apply(simp add: replicate_Suc[THEN sym] exp_ind del: replicate_Suc)
  done

lemma wprepare_loop_start_in_middle_2_Oc[simp]:  "wprepare_goto_start_pos m (a # aa # listaa) (b, Oc # list)
       \<Longrightarrow>wprepare_loop_start_in_middle m (a # aa # listaa) (Oc # b, list)"
  apply(auto simp: wprepare_goto_start_pos.simps
      wprepare_loop_start_in_middle.simps) apply(rename_tac rn)
  apply(rule_tac x = rn in exI, simp)
  apply(simp add: exp_ind[THEN sym])
  apply(rule_tac x = a in exI, rule_tac x = "aa#listaa" in exI, simp)
  apply(simp add: tape_of_nl_cons)
  done

lemma wprepare_loop_start_Oc2[simp]: "\<lbrakk>lm \<noteq> []; wprepare_goto_start_pos m lm (b, Oc # list)\<rbrakk>
       \<Longrightarrow> wprepare_loop_start m lm (Oc # b, list)"
  by(cases lm;cases "tl lm", auto simp add: wprepare_loop_start.simps)

lemma wprepare_add_one2_Oc_nonempty[simp]: "wprepare_add_one2 m lm (b, Oc # list) \<Longrightarrow> b \<noteq> []"
  apply(auto simp: wprepare_add_one2.simps)
  done

lemma add_one_2_stop:
  "wprepare_add_one2 m lm (b, Oc # list)      
  \<Longrightarrow>  wprepare_stop m lm (tl b, hd b # Oc # list)"
  apply(simp add: wprepare_add_one2.simps)
  done

declare wprepare_stop.simps[simp del]

lemma wprepare_correctness:
  assumes h: "lm \<noteq> []"
  shows "let P = (\<lambda> (st, l, r). st = 0) in 
  let Q = (\<lambda> (st, l, r). wprepare_inv st m lm (l, r)) in 
  let f = (\<lambda> stp. steps0 (Suc 0, [], (<m # lm>)) t_wcode_prepare stp) in
    \<exists> n .P (f n) \<and> Q (f n)"
proof -
  let ?P = "(\<lambda> (st, l, r). st = 0)"
  let ?Q = "(\<lambda> (st, l, r). wprepare_inv st m lm (l, r))"
  let ?f = "(\<lambda> stp. steps0 (Suc 0, [], (<m # lm>)) t_wcode_prepare stp)"
  have "\<exists> n. ?P (?f n) \<and> ?Q (?f n)"
  proof(rule_tac halt_lemma2)
    show "\<forall> n. \<not> ?P (?f n) \<and> ?Q (?f n) \<longrightarrow> 
                 ?Q (?f (Suc n)) \<and> (?f (Suc n), ?f n) \<in> wcode_prepare_le"
      using h
      apply(rule_tac allI, rule_tac impI) apply(rename_tac n)
      apply(case_tac "?f n", simp add: step.simps) apply(rename_tac c)
      apply(case_tac c, simp, case_tac [2] aa)
        apply(simp_all add: wprepare_inv.simps wcode_prepare_le_def lex_triple_def lex_pair_def
          split: if_splits) (* slow *)
         apply(simp_all add: start_2_goon  start_2_start
          add_one_2_add_one add_one_2_stop)
      apply(auto simp: wprepare_add_one2.simps)
      done
  qed (auto simp add: steps.simps wprepare_inv.simps wprepare_invs)
  thus "?thesis"
    apply(auto)
    done
qed

lemma tm_wf_t_wcode_prepare[intro]: "tm_wf (t_wcode_prepare, 0)"
  apply(simp add:tm_wf.simps t_wcode_prepare_def)
  done

lemma is_28_even[intro]: "(28 + (length t_twice_compile + length t_fourtimes_compile)) mod 2 = 0"
  by(auto simp: t_twice_compile_def t_fourtimes_compile_def)

lemma b_le_28[elim]: "(a, b) \<in> set t_wcode_main_first_part \<Longrightarrow>
  b \<le> (28 + (length t_twice_compile + length t_fourtimes_compile)) div 2"
  apply(auto simp: t_wcode_main_first_part_def t_twice_def)
  done



lemma tm_wf_change_termi:
  assumes "tm_wf (tp, 0)"
  shows "list_all (\<lambda>(acn, st). (st \<le> Suc (length tp div 2))) (adjust0 tp)"
proof -
  { fix acn st n
    assume "tp ! n = (acn, st)" "n < length tp" "0 < st"
    hence "(acn, st)\<in>set tp" by (metis nth_mem)
    with assms tm_wf.simps have "st \<le> length tp div 2 + 0" by auto
    hence "st \<le> Suc (length tp div 2)" by auto
  }
  thus ?thesis
    by(auto simp: tm_wf.simps List.list_all_length adjust.simps split: if_splits prod.split)
qed

lemma tm_wf_shift:
  assumes "list_all (\<lambda>(acn, st). (st \<le> y)) tp"
  shows "list_all (\<lambda>(acn, st). (st \<le> y + off)) (shift tp off)"
proof -
  have [dest!]:"\<And> P Q n. \<forall>n. Q n \<longrightarrow> P n \<Longrightarrow> Q n \<Longrightarrow> P n" by metis
  from assms show ?thesis by(auto simp: tm_wf.simps List.list_all_length shift.simps)
qed

declare length_tp'[simp del]

lemma length_mopup_1[simp]: "length (mopup (Suc 0)) = 16"
  apply(auto simp: mopup.simps)
  done

lemma twice_plus_28_elim[elim]: "(a, b) \<in> set (shift (adjust0 t_twice_compile) 12) \<Longrightarrow> 
  b \<le> (28 + (length t_twice_compile + length t_fourtimes_compile)) div 2"
  apply(simp add: t_twice_compile_def t_fourtimes_compile_def)
proof -
  assume g: "(a, b)
    \<in> set (shift
            (adjust
              (tm_of abc_twice @
               shift (mopup (Suc 0)) (length (tm_of abc_twice) div 2))
              (Suc ((length (tm_of abc_twice) + 16) div 2)))
            12)"
  moreover have "length (tm_of abc_twice) mod 2 = 0" by auto
  moreover have "length (tm_of abc_fourtimes) mod 2 = 0" by auto
  ultimately have "list_all (\<lambda>(acn, st). (st \<le> (60 + (length (tm_of abc_twice) + length (tm_of abc_fourtimes))) div 2)) 
    (shift (adjust0 t_twice_compile) 12)"
  proof(auto simp add: mod_ex1 del: adjust.simps)
    assume "even (length (tm_of abc_twice))"
    then obtain q where q:"length (tm_of abc_twice) = 2 * q" by auto
    assume "even (length (tm_of abc_fourtimes))"
    then obtain qa where qa:"length (tm_of abc_fourtimes) = 2 * qa" by auto
    note h = q qa
    hence "list_all (\<lambda>(acn, st). st \<le> (18 + (q + qa)) + 12) (shift (adjust0 t_twice_compile) 12)"
    proof(rule_tac tm_wf_shift t_twice_compile_def)
      have "list_all (\<lambda>(acn, st). st \<le> Suc (length t_twice_compile div 2)) (adjust0 t_twice_compile)"
        by(rule_tac tm_wf_change_termi, auto)
      thus "list_all (\<lambda>(acn, st). st \<le> 18 + (q + qa)) (adjust0 t_twice_compile)"
        using h
        apply(simp add: t_twice_compile_def, auto simp: List.list_all_length)
        done
    qed
    thus "list_all (\<lambda>(acn, st). st \<le> 30 + (length (tm_of abc_twice) div 2 + length (tm_of abc_fourtimes) div 2))
     (shift (adjust0 t_twice_compile) 12)" using h
      by simp
  qed
  thus "b \<le> (60 + (length (tm_of abc_twice) + length (tm_of abc_fourtimes))) div 2"
    using g
    apply(auto simp:t_twice_compile_def)
    apply(simp add: Ball_set[THEN sym])
    apply(erule_tac x = "(a, b)" in ballE, simp, simp)
    done
qed 

lemma length_plus_28_elim2[elim]: "(a, b) \<in> set (shift (adjust0 t_fourtimes_compile) (t_twice_len + 13)) 
  \<Longrightarrow> b \<le> (28 + (length t_twice_compile + length t_fourtimes_compile)) div 2"
  apply(simp add: t_twice_compile_def t_fourtimes_compile_def t_twice_len_def)
proof -
  assume g: "(a, b)
    \<in> set (shift
             (adjust (tm_of abc_fourtimes @ shift (mopup (Suc 0)) (length (tm_of abc_fourtimes) div 2))
               (Suc ((length (tm_of abc_fourtimes) + 16) div 2)))
             (length t_twice div 2 + 13))"
  moreover have "length (tm_of abc_twice) mod 2 = 0" by auto
  moreover have "length (tm_of abc_fourtimes) mod 2 = 0" by auto
  ultimately have "list_all (\<lambda>(acn, st). (st \<le> (60 + (length (tm_of abc_twice) + length (tm_of abc_fourtimes))) div 2)) 
    (shift (adjust0 (tm_of abc_fourtimes @ shift (mopup (Suc 0))
    (length (tm_of abc_fourtimes) div 2))) (length t_twice div 2 + 13))"
  proof(auto simp: mod_ex1 t_twice_def t_twice_compile_def)
    assume "even (length (tm_of abc_twice))"
    then obtain q where q:"length (tm_of abc_twice) = 2 * q" by auto
    assume "even (length (tm_of abc_fourtimes))"
    then obtain qa where qa:"length (tm_of abc_fourtimes) = 2 * qa" by auto
    note h = q qa
    hence "list_all (\<lambda>(acn, st). st \<le> (9 + qa + (21 + q)))
      (shift (adjust0 (tm_of abc_fourtimes @ shift (mopup (Suc 0)) qa)) (21 + q))"
    proof(rule_tac tm_wf_shift t_twice_compile_def)
      have "list_all (\<lambda>(acn, st). st \<le> Suc (length (tm_of abc_fourtimes @ shift 
        (mopup (Suc 0)) qa) div 2)) (adjust0 (tm_of abc_fourtimes @ shift (mopup (Suc 0)) qa))"
        apply(rule_tac tm_wf_change_termi)
        using wf_fourtimes h
        apply(simp add: t_fourtimes_compile_def)
        done
      thus "list_all (\<lambda>(acn, st). st \<le> 9 + qa)
        (adjust (tm_of abc_fourtimes @ shift (mopup (Suc 0)) qa)
          (Suc (length (tm_of abc_fourtimes @ shift (mopup (Suc 0)) qa) div
                2)))"
        using h
        apply(simp)
        done
    qed
    thus "list_all
     (\<lambda>(acn, st). st \<le> 30 + (length (tm_of abc_twice) div 2 + length (tm_of abc_fourtimes) div 2))
     (shift
       (adjust (tm_of abc_fourtimes @ shift (mopup (Suc 0)) (length (tm_of abc_fourtimes) div 2))
         (9 + length (tm_of abc_fourtimes) div 2))
       (21 + length (tm_of abc_twice) div 2))"
      apply(subgoal_tac "qa + q = q + qa")
       apply(simp add: h)
      apply(simp)
      done
  qed
  thus "b \<le> (60 + (length (tm_of abc_twice) + length (tm_of abc_fourtimes))) div 2"
    using g
    apply(simp add: Ball_set[THEN sym])
    apply(erule_tac x = "(a, b)" in ballE, simp, simp)
    done
qed

lemma tm_wf_t_wcode_main[intro]: "tm_wf (t_wcode_main, 0)"
  by(auto simp: t_wcode_main_def tm_wf.simps
      t_twice_def t_fourtimes_def del: List.list_all_iff)

declare tm_comp.simps[simp del]

lemma prepare_mainpart_lemma:
  "args \<noteq> [] \<Longrightarrow> 
  \<exists> stp ln rn. steps0 (Suc 0, [], <m # args>) (t_wcode_prepare |+| t_wcode_main) stp
              = (0,  Bk # Oc\<up>(Suc m), Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(bl_bin (<args>)) @ Bk\<up>(rn))"
proof -
  let ?P1 = "(\<lambda> (l, r). (l::cell list) = [] \<and> r = <m # args>)"
  let ?Q1 = "(\<lambda> (l, r). wprepare_stop m args (l, r))"
  let ?P2 = ?Q1
  let ?Q2 = "(\<lambda> (l, r). (\<exists> ln rn. l = Bk # Oc\<up>(Suc m) \<and>
                           r =  Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(bl_bin (<args>)) @ Bk\<up>(rn)))"
  let ?P3 = "\<lambda> tp. False"
  assume h: "args \<noteq> []"
  have "{?P1} t_wcode_prepare |+| t_wcode_main {?Q2}"
  proof(rule_tac Hoare_plus_halt)
    show "{?P1} t_wcode_prepare {?Q1}"
    proof(rule_tac Hoare_haltI, auto)
      show "\<exists>n. is_final (steps0 (Suc 0, [], <m # args>) t_wcode_prepare n) \<and>
        wprepare_stop m args holds_for steps0 (Suc 0, [], <m # args>) t_wcode_prepare n"
        using wprepare_correctness[of args m,OF h]
        apply(auto simp add: wprepare_inv.simps)
        by (metis holds_for.simps is_finalI)
    qed
  next
    show "{?P2} t_wcode_main {?Q2}"
    proof(rule_tac Hoare_haltI, auto)
      fix l r
      assume "wprepare_stop m args (l, r)"
      thus "\<exists>n. is_final (steps0 (Suc 0, l, r) t_wcode_main n) \<and>
              (\<lambda>(l, r). l = Bk # Oc # Oc \<up> m \<and> (\<exists>ln rn. r = Bk # Oc # Bk \<up> ln @ 
        Bk # Bk # Oc \<up> bl_bin (<args>) @ Bk \<up> rn)) holds_for steps0 (Suc 0, l, r) t_wcode_main n"
      proof(auto simp: wprepare_stop.simps)
        fix rn
        show " \<exists>n. is_final (steps0 (Suc 0, Bk # <rev args> @ Bk # Bk # Oc # Oc \<up> m, Bk # Oc # Bk \<up> rn) t_wcode_main n) \<and>
          (\<lambda>(l, r). l = Bk # Oc # Oc \<up> m \<and>
          (\<exists>ln rn. r = Bk # Oc # Bk \<up> ln @
          Bk # Bk # Oc \<up> bl_bin (<args>) @
          Bk \<up> rn)) holds_for steps0 (Suc 0, Bk # <rev args> @ Bk # Bk # Oc # Oc \<up> m, Bk # Oc # Bk \<up> rn) t_wcode_main n"
          using t_wcode_main_lemma_pre[of "args" "<args>" 0 "Oc\<up>(Suc m)" 0 rn,OF h refl]
          apply(auto simp: tape_of_nl_rev)
          apply(rename_tac stp ln rna)
          apply(rule_tac x = stp in exI, auto)
          done
      qed
    qed
  next
    show "tm_wf0 t_wcode_prepare"
      by auto
  qed
  then obtain n 
    where "\<And> tp. (case tp of (l, r) \<Rightarrow> l = [] \<and> r = <m # args>) \<longrightarrow>
       (is_final (steps0 (1, tp) (t_wcode_prepare |+| t_wcode_main) n) \<and>
            (\<lambda>(l, r).
                \<exists>ln rn.
                   l = Bk # Oc \<up> Suc m \<and>
                   r = Bk # Oc # Bk \<up> ln @ Bk # Bk # Oc \<up> bl_bin (<args>) @ Bk \<up> rn) holds_for steps0 (1, tp) (t_wcode_prepare |+| t_wcode_main) n)"
    unfolding Hoare_halt_def by auto
  thus "?thesis"
    apply(rule_tac x = n in exI)
    apply(case_tac "(steps0 (Suc 0, [], <m # args>)
      (adjust0 t_wcode_prepare @ shift t_wcode_main (length t_wcode_prepare div 2)) n)")
    apply(auto simp: tm_comp.simps)
    done
qed

definition tinres :: "cell list \<Rightarrow> cell list \<Rightarrow> bool"
  where
    "tinres xs ys = (\<exists>n. xs = ys @ Bk \<up> n \<or> ys = xs @ Bk \<up> n)"

lemma tinres_fetch_congr[simp]:  "tinres r r' \<Longrightarrow> 
  fetch t ss (read r) = 
  fetch t ss (read r')"
  apply(simp add: fetch.simps, auto split: if_splits simp: tinres_def)
  using hd_replicate apply fastforce
  using hd_replicate apply fastforce
  done

lemma nonempty_hd_tinres[simp]: "\<lbrakk>tinres r r'; r \<noteq> []; r' \<noteq> []\<rbrakk> \<Longrightarrow> hd r = hd r'"
  apply(auto simp: tinres_def)
  done

lemma tinres_nonempty[simp]:
  "\<lbrakk>tinres r []; r \<noteq> []\<rbrakk> \<Longrightarrow> hd r = Bk"
  "\<lbrakk>tinres [] r'; r' \<noteq> []\<rbrakk> \<Longrightarrow> hd r' = Bk"
  "\<lbrakk>tinres r [];  r \<noteq> []\<rbrakk> \<Longrightarrow> tinres (tl r) []"
  "tinres r r' \<Longrightarrow> tinres (b # r) (b # r')"
  by(auto simp: tinres_def)

lemma ex_move_tl[intro]: "\<exists>na. tl r = tl (r @ Bk\<up>(n)) @ Bk\<up>(na) \<or> tl (r @ Bk\<up>(n)) = tl r @ Bk\<up>(na)"
  apply(case_tac r, simp)
  by(case_tac n, auto)

lemma tinres_tails[simp]: "tinres r r' \<Longrightarrow> tinres (tl r) (tl r')"
  apply(auto simp: tinres_def)
  by(case_tac r', auto)

lemma tinres_empty[simp]: 
  "\<lbrakk>tinres [] r'\<rbrakk> \<Longrightarrow> tinres [] (tl r')"
  "tinres r [] \<Longrightarrow> tinres (Bk # tl r) [Bk]"
  "tinres r [] \<Longrightarrow> tinres (Oc # tl r) [Oc]"
  by(auto simp: tinres_def)

lemma tinres_step2:
  assumes "tinres r r'" "step0 (ss, l, r) t = (sa, la, ra)" "step0 (ss, l, r') t = (sb, lb, rb)"
  shows "la = lb \<and> tinres ra rb \<and> sa = sb"
proof (cases "fetch t ss (read r')")
  case (Pair a b)
  have sa:"sa = sb" using assms Pair by(force simp: step.simps)
  have "la = lb \<and> tinres ra rb" using assms Pair
    by(cases a, auto simp: step.simps split: if_splits)
  thus ?thesis using sa by auto
qed

lemma tinres_steps2: 
  "\<lbrakk>tinres r r'; steps0 (ss, l, r) t stp = (sa, la, ra); steps0 (ss, l, r') t stp = (sb, lb, rb)\<rbrakk>
    \<Longrightarrow> la = lb \<and> tinres ra rb \<and> sa = sb"
proof(induct stp arbitrary: sa la ra sb lb rb)
  case (Suc stp sa la ra sb lb rb)
  then show ?case 
    apply(simp)
    apply(case_tac "(steps0 (ss, l, r) t stp)")
    apply(case_tac "(steps0 (ss, l, r') t stp)")
  proof -
    fix stp a b c aa ba ca
    assume ind: "\<And>sa la ra sb lb rb. \<lbrakk>steps0 (ss, l, r) t stp = (sa, la, ra); 
    steps0 (ss, l, r') t stp = (sb, lb, rb)\<rbrakk> \<Longrightarrow> la = lb \<and> tinres ra rb \<and> sa = sb"
      and h: " tinres r r'" "step0 (steps0 (ss, l, r) t stp) t = (sa, la, ra)"
      "step0 (steps0 (ss, l, r') t stp) t = (sb, lb, rb)" "steps0 (ss, l, r) t stp = (a, b, c)" 
      "steps0 (ss, l, r') t stp = (aa, ba, ca)"
    have "b = ba \<and> tinres c ca \<and> a = aa"
      apply(rule_tac ind, simp_all add: h)
      done
    thus "la = lb \<and> tinres ra rb \<and> sa = sb"
      apply(rule_tac l = b  and r = c  and ss = a and r' = ca   
          and t = t in tinres_step2)
      using h
        apply(simp, simp, simp)
      done
  qed
qed (simp add: steps.simps)


definition t_wcode_adjust :: "instr list"
  where
    "t_wcode_adjust = [(W1, 1), (R, 2), (Nop, 2), (R, 3), (R, 3), (R, 4), 
                   (L, 8), (L, 5), (L, 6), (W0, 5), (L, 6), (R, 7), 
                   (W1, 2), (Nop, 7), (L, 9), (W0, 8), (L, 9), (L, 10), 
                    (L, 11), (L, 10), (R, 0), (L, 11)]"

lemma fetch_t_wcode_adjust[simp]:
  "fetch t_wcode_adjust (Suc 0) Bk = (W1, 1)"
  "fetch t_wcode_adjust (Suc 0) Oc = (R, 2)"
  "fetch t_wcode_adjust (Suc (Suc 0)) Oc = (R, 3)"
  "fetch t_wcode_adjust (Suc (Suc (Suc 0))) Oc = (R, 4)"
  "fetch t_wcode_adjust  (Suc (Suc (Suc 0))) Bk = (R, 3)"
  "fetch t_wcode_adjust 4 Bk = (L, 8)"
  "fetch t_wcode_adjust 4 Oc = (L, 5)"
  "fetch t_wcode_adjust 5 Oc = (W0, 5)"
  "fetch t_wcode_adjust 5 Bk = (L, 6)"
  "fetch t_wcode_adjust 6 Oc = (R, 7)"
  "fetch t_wcode_adjust 6 Bk = (L, 6)"
  "fetch t_wcode_adjust 7 Bk = (W1, 2)"
  "fetch t_wcode_adjust 8 Bk = (L, 9)"
  "fetch t_wcode_adjust 8 Oc = (W0, 8)"
  "fetch t_wcode_adjust 9 Oc = (L, 10)"
  "fetch t_wcode_adjust 9 Bk = (L, 9)"
  "fetch t_wcode_adjust 10 Bk = (L, 11)"
  "fetch t_wcode_adjust 10 Oc = (L, 10)"
  "fetch t_wcode_adjust 11 Oc = (L, 11)"
  "fetch t_wcode_adjust 11 Bk = (R, 0)"
  by(auto simp: fetch.simps t_wcode_adjust_def nth_of.simps numeral)


fun wadjust_start :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_start m rs (l, r) = 
         (\<exists> ln rn. l = Bk # Oc\<up>(Suc m) \<and>
                   tl r = Oc # Bk\<up>(ln) @ Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn))"

fun wadjust_loop_start :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_loop_start m rs (l, r) = 
          (\<exists> ln rn ml mr. l = Oc\<up>(ml) @ Bk # Oc\<up>(Suc m)  \<and>
                          r = Oc # Bk\<up>(ln) @ Bk # Oc\<up>(mr) @ Bk\<up>(rn) \<and>
                          ml + mr = Suc (Suc rs) \<and> mr > 0)"

fun wadjust_loop_right_move :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_loop_right_move m rs (l, r) = 
   (\<exists> ml mr nl nr rn. l = Bk\<up>(nl) @ Oc # Oc\<up>(ml) @ Bk # Oc\<up>(Suc m) \<and>
                      r = Bk\<up>(nr) @ Oc\<up>(mr) @ Bk\<up>(rn) \<and>
                      ml + mr = Suc (Suc rs) \<and> mr > 0 \<and>
                      nl + nr > 0)"

fun wadjust_loop_check :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_loop_check m rs (l, r) = 
  (\<exists> ml mr ln rn. l = Oc # Bk\<up>(ln) @ Bk # Oc # Oc\<up>(ml) @ Bk # Oc\<up>(Suc m) \<and>
                  r = Oc\<up>(mr) @ Bk\<up>(rn) \<and> ml + mr = (Suc rs))"

fun wadjust_loop_erase :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_loop_erase m rs (l, r) = 
    (\<exists> ml mr ln rn. l = Bk\<up>(ln) @ Bk # Oc # Oc\<up>(ml) @ Bk # Oc\<up>(Suc m) \<and>
                    tl r = Oc\<up>(mr) @ Bk\<up>(rn) \<and> ml + mr = (Suc rs) \<and> mr > 0)"

fun wadjust_loop_on_left_moving_O :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_loop_on_left_moving_O m rs (l, r) = 
      (\<exists> ml mr ln rn. l = Oc\<up>(ml) @ Bk # Oc\<up>(Suc m )\<and>
                      r = Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(mr) @ Bk\<up>(rn) \<and>
                      ml + mr = Suc rs \<and> mr > 0)"

fun wadjust_loop_on_left_moving_B :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_loop_on_left_moving_B m rs (l, r) = 
      (\<exists> ml mr nl nr rn. l = Bk\<up>(nl) @ Oc # Oc\<up>(ml) @ Bk # Oc\<up>(Suc m) \<and>
                         r = Bk\<up>(nr) @ Bk # Bk # Oc\<up>(mr) @ Bk\<up>(rn) \<and> 
                         ml + mr = Suc rs \<and> mr > 0)"

fun wadjust_loop_on_left_moving :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_loop_on_left_moving m rs (l, r) = 
       (wadjust_loop_on_left_moving_O m rs (l, r) \<or>
       wadjust_loop_on_left_moving_B m rs (l, r))"

fun wadjust_loop_right_move2 :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_loop_right_move2 m rs (l, r) = 
        (\<exists> ml mr ln rn. l = Oc # Oc\<up>(ml) @ Bk # Oc\<up>(Suc m) \<and>
                        r = Bk\<up>(ln) @ Bk # Bk # Oc\<up>(mr) @ Bk\<up>(rn) \<and>
                        ml + mr = Suc rs \<and> mr > 0)"

fun wadjust_erase2 :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_erase2 m rs (l, r) = 
     (\<exists> ln rn. l = Bk\<up>(ln) @ Bk # Oc # Oc\<up>(Suc rs) @ Bk # Oc\<up>(Suc m) \<and>
                     tl r = Bk\<up>(rn))"

fun wadjust_on_left_moving_O :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_on_left_moving_O m rs (l, r) = 
        (\<exists> rn. l = Oc\<up>(Suc rs) @ Bk # Oc\<up>(Suc m) \<and>
                  r = Oc # Bk\<up>(rn))"

fun wadjust_on_left_moving_B :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_on_left_moving_B m rs (l, r) = 
         (\<exists> ln rn. l = Bk\<up>(ln) @ Oc # Oc\<up>(Suc rs) @ Bk # Oc\<up>(Suc m) \<and>
                   r = Bk\<up>(rn))"

fun wadjust_on_left_moving :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_on_left_moving m rs (l, r) = 
      (wadjust_on_left_moving_O m rs (l, r) \<or>
       wadjust_on_left_moving_B m rs (l, r))"

fun wadjust_goon_left_moving_B :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where 
    "wadjust_goon_left_moving_B m rs (l, r) = 
        (\<exists> rn. l = Oc\<up>(Suc m) \<and> 
               r = Bk # Oc\<up>(Suc (Suc rs)) @ Bk\<up>(rn))"

fun wadjust_goon_left_moving_O :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_goon_left_moving_O m rs (l, r) = 
      (\<exists> ml mr rn. l = Oc\<up>(ml) @ Bk # Oc\<up>(Suc m) \<and>
                      r = Oc\<up>(mr) @ Bk\<up>(rn) \<and> 
                      ml + mr = Suc (Suc rs) \<and> mr > 0)"

fun wadjust_goon_left_moving :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_goon_left_moving m rs (l, r) = 
            (wadjust_goon_left_moving_B m rs (l, r) \<or>
             wadjust_goon_left_moving_O m rs (l, r))"

fun wadjust_backto_standard_pos_B :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_backto_standard_pos_B m rs (l, r) =
        (\<exists> rn. l = [] \<and> 
               r = Bk # Oc\<up>(Suc m )@ Bk # Oc\<up>(Suc (Suc rs)) @ Bk\<up>(rn))"

fun wadjust_backto_standard_pos_O :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_backto_standard_pos_O m rs (l, r) = 
      (\<exists> ml mr rn. l = Oc\<up>(ml) \<and>
                      r = Oc\<up>(mr) @ Bk # Oc\<up>(Suc (Suc rs)) @ Bk\<up>(rn) \<and> 
                      ml + mr = Suc m \<and> mr > 0)"

fun wadjust_backto_standard_pos :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_backto_standard_pos m rs (l, r) = 
        (wadjust_backto_standard_pos_B m rs (l, r) \<or> 
        wadjust_backto_standard_pos_O m rs (l, r))"

fun wadjust_stop :: "nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_stop m rs (l, r) =
        (\<exists> rn. l = [Bk] \<and> 
               r = Oc\<up>(Suc m )@ Bk # Oc\<up>(Suc (Suc rs)) @ Bk\<up>(rn))"

declare wadjust_start.simps[simp del]  wadjust_loop_start.simps[simp del]
  wadjust_loop_right_move.simps[simp del]  wadjust_loop_check.simps[simp del]
  wadjust_loop_erase.simps[simp del] wadjust_loop_on_left_moving.simps[simp del]
  wadjust_loop_right_move2.simps[simp del] wadjust_erase2.simps[simp del]
  wadjust_on_left_moving_O.simps[simp del] wadjust_on_left_moving_B.simps[simp del]
  wadjust_on_left_moving.simps[simp del] wadjust_goon_left_moving_B.simps[simp del]
  wadjust_goon_left_moving_O.simps[simp del] wadjust_goon_left_moving.simps[simp del]
  wadjust_backto_standard_pos.simps[simp del] wadjust_backto_standard_pos_B.simps[simp del]
  wadjust_backto_standard_pos_O.simps[simp del] wadjust_stop.simps[simp del]

fun wadjust_inv :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tape \<Rightarrow> bool"
  where
    "wadjust_inv st m rs (l, r) = 
       (if st = Suc 0 then wadjust_start m rs (l, r) 
        else if st = Suc (Suc 0) then wadjust_loop_start m rs (l, r)
        else if st = Suc (Suc (Suc 0)) then wadjust_loop_right_move m rs (l, r)
        else if st = 4 then wadjust_loop_check m rs (l, r)
        else if st = 5 then wadjust_loop_erase m rs (l, r)
        else if st = 6 then wadjust_loop_on_left_moving m rs (l, r)
        else if st = 7 then wadjust_loop_right_move2 m rs (l, r)
        else if st = 8 then wadjust_erase2 m rs (l, r)
        else if st = 9 then wadjust_on_left_moving m rs (l, r)
        else if st = 10 then wadjust_goon_left_moving m rs (l, r)
        else if st = 11 then wadjust_backto_standard_pos m rs (l, r)
        else if st = 0 then wadjust_stop m rs (l, r)
        else False
)"

declare wadjust_inv.simps[simp del]

fun wadjust_phase :: "nat \<Rightarrow> config \<Rightarrow> nat"
  where
    "wadjust_phase rs (st, l, r) = 
         (if st = 1 then 3 
          else if st \<ge> 2 \<and> st \<le> 7 then 2
          else if st \<ge> 8 \<and> st \<le> 11 then 1
          else 0)"

fun wadjust_stage :: "nat \<Rightarrow> config \<Rightarrow> nat"
  where
    "wadjust_stage rs (st, l, r) = 
           (if st \<ge> 2 \<and> st \<le> 7 then 
                  rs - length (takeWhile (\<lambda> a. a = Oc) 
                          (tl (dropWhile (\<lambda> a. a = Oc) (rev l @ r))))
            else 0)"

fun wadjust_state :: "nat \<Rightarrow> config \<Rightarrow> nat"
  where
    "wadjust_state rs (st, l, r) = 
       (if st \<ge> 2 \<and> st \<le> 7 then 8 - st
        else if st \<ge> 8 \<and> st \<le> 11 then 12 - st
        else 0)"

fun wadjust_step :: "nat \<Rightarrow> config \<Rightarrow> nat"
  where
    "wadjust_step rs (st, l, r) = 
       (if st = 1 then (if hd r = Bk then 1
                        else 0) 
        else if st = 3 then length r
        else if st = 5 then (if hd r = Oc then 1
                             else 0)
        else if st = 6 then length l
        else if st = 8 then (if hd r = Oc then 1
                             else 0)
        else if st = 9 then length l
        else if st = 10 then length l
        else if st = 11 then (if hd r = Bk then 0
                              else Suc (length l))
        else 0)"

fun wadjust_measure :: "(nat \<times> config) \<Rightarrow> nat \<times> nat \<times> nat \<times> nat"
  where
    "wadjust_measure (rs, (st, l, r)) = 
     (wadjust_phase rs (st, l, r), 
      wadjust_stage rs (st, l, r),
      wadjust_state rs (st, l, r), 
      wadjust_step rs (st, l, r))"

definition wadjust_le :: "((nat \<times> config) \<times> nat \<times> config) set"
  where "wadjust_le \<equiv> (inv_image lex_square wadjust_measure)"

lemma wf_lex_square[intro]: "wf lex_square"
  by(auto intro:wf_lex_prod simp: Abacus.lex_pair_def lex_square_def 
      Abacus.lex_triple_def)

lemma wf_wadjust_le[intro]: "wf wadjust_le"
  by(auto intro:wf_inv_image simp: wadjust_le_def
      Abacus.lex_triple_def Abacus.lex_pair_def)

lemma wadjust_start_snd_nonempty[simp]: "wadjust_start m rs (c, []) = False"
  apply(auto simp: wadjust_start.simps)
  done

lemma wadjust_loop_right_move_fst_nonempty[simp]: "wadjust_loop_right_move m rs (c, []) \<Longrightarrow> c \<noteq> []"
  apply(auto simp: wadjust_loop_right_move.simps)
  done

lemma wadjust_loop_check_fst_nonempty[simp]: "wadjust_loop_check m rs (c, []) \<Longrightarrow> c \<noteq> []"
  apply(simp only: wadjust_loop_check.simps, auto)
  done

lemma wadjust_loop_start_snd_nonempty[simp]: "wadjust_loop_start m rs (c, []) = False"
  apply(simp add: wadjust_loop_start.simps)
  done

lemma wadjust_erase2_singleton[simp]: "wadjust_loop_check m rs (c, []) \<Longrightarrow> wadjust_erase2 m rs (tl c, [hd c])"
  apply(simp only: wadjust_loop_check.simps wadjust_erase2.simps, auto)
  done

lemma wadjust_loop_on_left_moving_snd_nonempty[simp]:
  "wadjust_loop_on_left_moving m rs (c, []) = False"
  "wadjust_loop_right_move2 m rs (c, []) = False"
  "wadjust_erase2 m rs ([], []) = False"
  by(auto simp: wadjust_loop_on_left_moving.simps
      wadjust_loop_right_move2.simps
      wadjust_erase2.simps)

lemma wadjust_on_left_moving_B_Bk1[simp]: "wadjust_on_left_moving_B m rs 
                 (Oc # Oc # Oc\<up>(rs) @ Bk # Oc # Oc\<up>(m), [Bk])"
  apply(simp add: wadjust_on_left_moving_B.simps, auto)
  done

lemma wadjust_on_left_moving_B_Bk2[simp]: "wadjust_on_left_moving_B m rs 
                 (Bk\<up>(n) @ Bk # Oc # Oc # Oc\<up>(rs) @ Bk # Oc # Oc\<up>(m), [Bk])"
  apply(simp add: wadjust_on_left_moving_B.simps , auto)
  apply(rule_tac x = "Suc n" in exI, simp add: exp_ind del: replicate_Suc)
  done

lemma wadjust_on_left_moving_singleton[simp]: "\<lbrakk>wadjust_erase2 m rs (c, []); c \<noteq> []\<rbrakk> \<Longrightarrow>
            wadjust_on_left_moving m rs (tl c, [hd c])" unfolding wadjust_erase2.simps
  apply(auto simp add: wadjust_on_left_moving.simps)
   apply (metis (no_types, lifting) empty_replicate hd_append hd_replicate list.sel(1) list.sel(3)
      self_append_conv2 tl_append2 tl_replicate
      wadjust_on_left_moving_B_Bk1 wadjust_on_left_moving_B_Bk2)+
  done

lemma wadjust_erase2_cases[simp]: "wadjust_erase2 m rs (c, [])
    \<Longrightarrow> (c = [] \<longrightarrow> wadjust_on_left_moving m rs ([], [Bk])) \<and> 
       (c \<noteq> [] \<longrightarrow> wadjust_on_left_moving m rs (tl c, [hd c]))"
  apply(auto)
  done

lemma wadjust_on_left_moving_nonempty[simp]:
  "wadjust_on_left_moving m rs ([], []) = False"
  "wadjust_on_left_moving_O m rs (c, []) = False"
   apply(auto simp: wadjust_on_left_moving.simps 
      wadjust_on_left_moving_O.simps wadjust_on_left_moving_B.simps)
  done

lemma wadjust_on_left_moving_B_singleton_Bk[simp]:
  " \<lbrakk>wadjust_on_left_moving_B m rs (c, []); c \<noteq> []; hd c = Bk\<rbrakk> \<Longrightarrow>
                                      wadjust_on_left_moving_B m rs (tl c, [Bk])"
  apply(auto simp add: wadjust_on_left_moving_B.simps hd_append)
  by (metis cell.distinct(1) empty_replicate list.sel(1) tl_append2 tl_replicate)

lemma wadjust_on_left_moving_B_singleton_Oc[simp]:
  "\<lbrakk>wadjust_on_left_moving_B m rs (c, []); c \<noteq> []; hd c = Oc\<rbrakk> \<Longrightarrow>
                                  wadjust_on_left_moving_O m rs (tl c, [Oc])"
  apply(auto simp add: wadjust_on_left_moving_B.simps wadjust_on_left_moving_O.simps hd_append)
   apply (metis cell.distinct(1) empty_replicate hd_replicate list.sel(3) self_append_conv2)+
  done

lemma wadjust_on_left_moving_singleton2[simp]:
  "\<lbrakk>wadjust_on_left_moving m rs (c, []); c \<noteq> []\<rbrakk> \<Longrightarrow> 
  wadjust_on_left_moving m rs (tl c, [hd c])"
  apply(simp add: wadjust_on_left_moving.simps)
  apply(case_tac "hd c", simp_all)
  done

lemma wadjust_nonempty[simp]: "wadjust_goon_left_moving m rs (c, []) = False"
  "wadjust_backto_standard_pos m rs (c, []) = False"
  by(auto simp: wadjust_goon_left_moving.simps wadjust_goon_left_moving_B.simps
      wadjust_goon_left_moving_O.simps wadjust_backto_standard_pos.simps
      wadjust_backto_standard_pos_B.simps wadjust_backto_standard_pos_O.simps)

lemma wadjust_loop_start_no_Bk[simp]: "wadjust_loop_start m rs (c, Bk # list) = False"
  apply(auto simp: wadjust_loop_start.simps)
  done

lemma wadjust_loop_check_nonempty[simp]: "wadjust_loop_check m rs (c, b) \<Longrightarrow> c \<noteq> []"
  apply(simp only: wadjust_loop_check.simps, auto)
  done

lemma wadjust_erase2_via_loop_check_Bk[simp]: "wadjust_loop_check m rs (c, Bk # list)
              \<Longrightarrow>  wadjust_erase2 m rs (tl c, hd c # Bk # list)"
  by (auto simp: wadjust_loop_check.simps wadjust_erase2.simps)

declare wadjust_loop_on_left_moving_O.simps[simp del]
  wadjust_loop_on_left_moving_B.simps[simp del]

lemma wadjust_loop_on_left_moving_B_via_erase[simp]: "\<lbrakk>wadjust_loop_erase m rs (c, Bk # list); hd c = Bk\<rbrakk>
    \<Longrightarrow> wadjust_loop_on_left_moving_B m rs (tl c, Bk # Bk # list)"
  unfolding wadjust_loop_erase.simps wadjust_loop_on_left_moving_B.simps
  apply(erule_tac exE)+
  apply(rename_tac ml mr ln rn)
  apply(rule_tac x = ml in exI, rule_tac x = mr in exI, 
      rule_tac x = ln in exI, rule_tac x = 0 in exI)
  apply(case_tac ln, auto)
  apply(simp add: exp_ind [THEN sym])
  done

lemma wadjust_loop_on_left_moving_O_Bk_via_erase[simp]:
  "\<lbrakk>wadjust_loop_erase m rs (c, Bk # list); c \<noteq> []; hd c = Oc\<rbrakk> \<Longrightarrow>
             wadjust_loop_on_left_moving_O m rs (tl c, Oc # Bk # list)"
  apply(auto simp: wadjust_loop_erase.simps wadjust_loop_on_left_moving_O.simps)
  by (metis cell.distinct(1) empty_replicate hd_append hd_replicate list.sel(1))

lemma wadjust_loop_on_left_moving_Bk_via_erase[simp]: "\<lbrakk>wadjust_loop_erase m rs (c, Bk # list); c \<noteq> []\<rbrakk> \<Longrightarrow> 
                wadjust_loop_on_left_moving m rs (tl c, hd c # Bk # list)"
  apply(case_tac "hd c", simp_all add:wadjust_loop_on_left_moving.simps)
  done


lemma wadjust_loop_on_left_moving_B_Bk_move[simp]:
  "\<lbrakk>wadjust_loop_on_left_moving_B m rs (c, Bk # list); hd c = Bk\<rbrakk>
    \<Longrightarrow>  wadjust_loop_on_left_moving_B m rs (tl c, Bk # Bk # list)"
  apply(simp only: wadjust_loop_on_left_moving_B.simps)
  apply(erule_tac exE)+
  by (metis (no_types, lifting) cell.distinct(1) list.sel(1)
      replicate_Suc_iff_anywhere self_append_conv2 tl_append2 tl_replicate)

lemma wadjust_loop_on_left_moving_O_Oc_move[simp]:
  "\<lbrakk>wadjust_loop_on_left_moving_B m rs (c, Bk # list); hd c = Oc\<rbrakk>
    \<Longrightarrow> wadjust_loop_on_left_moving_O m rs (tl c, Oc # Bk # list)"
  apply(simp only: wadjust_loop_on_left_moving_O.simps 
      wadjust_loop_on_left_moving_B.simps)
  by (metis cell.distinct(1) empty_replicate hd_append hd_replicate list.sel(3) self_append_conv2)


lemma wadjust_loop_erase_nonempty[simp]: "wadjust_loop_erase m rs (c, b) \<Longrightarrow> c \<noteq> []"
  "wadjust_loop_on_left_moving m rs (c, b) \<Longrightarrow> c \<noteq> []"
  "wadjust_loop_right_move2 m rs (c, b) \<Longrightarrow> c \<noteq> []"
  "wadjust_erase2 m rs (c, Bk # list) \<Longrightarrow> c \<noteq> []"
  "wadjust_on_left_moving m rs (c,b) \<Longrightarrow> c \<noteq> []"
  "wadjust_on_left_moving_O m rs (c, Bk # list) = False"
  "wadjust_goon_left_moving m rs (c, b) \<Longrightarrow> c \<noteq> []"
  "wadjust_loop_on_left_moving_O m rs (c, Bk # list) = False"
  by(auto simp: wadjust_loop_erase.simps wadjust_loop_on_left_moving.simps 
      wadjust_loop_on_left_moving_O.simps wadjust_loop_on_left_moving_B.simps
      wadjust_loop_right_move2.simps wadjust_erase2.simps
      wadjust_on_left_moving.simps
      wadjust_on_left_moving_O.simps
      wadjust_on_left_moving_B.simps wadjust_goon_left_moving.simps
      wadjust_goon_left_moving_B.simps
      wadjust_goon_left_moving_O.simps)

lemma wadjust_loop_on_left_moving_Bk_move[simp]:
  "wadjust_loop_on_left_moving m rs (c, Bk # list)
            \<Longrightarrow> wadjust_loop_on_left_moving m rs (tl c, hd c # Bk # list)"
  apply(simp add: wadjust_loop_on_left_moving.simps)
  apply(case_tac "hd c", simp_all)
  done

lemma wadjust_loop_start_Oc_via_Bk_move[simp]: 
  "wadjust_loop_right_move2 m rs (c, Bk # list) \<Longrightarrow>  wadjust_loop_start m rs (c, Oc # list)"
  apply(auto simp: wadjust_loop_right_move2.simps wadjust_loop_start.simps replicate_app_Cons_same)
  by (metis add_Suc replicate_Suc)

lemma wadjust_on_left_moving_Bk_via_erase[simp]: "wadjust_erase2 m rs (c, Bk # list) \<Longrightarrow> 
                 wadjust_on_left_moving m rs (tl c, hd c # Bk # list)"
  apply(auto simp: wadjust_erase2.simps wadjust_on_left_moving.simps replicate_app_Cons_same
      wadjust_on_left_moving_O.simps wadjust_on_left_moving_B.simps)
   apply (metis exp_ind replicate_append_same)+
  done


lemma wadjust_on_left_moving_B_Bk_drop_one: "\<lbrakk>wadjust_on_left_moving_B m rs (c, Bk # list); hd c = Bk\<rbrakk>
    \<Longrightarrow> wadjust_on_left_moving_B m rs (tl c, Bk # Bk # list)"
  apply(auto simp: wadjust_on_left_moving_B.simps)
  by (metis cell.distinct(1) hd_append list.sel(1) tl_append2 tl_replicate)

lemma wadjust_on_left_moving_B_Bk_drop_Oc: "\<lbrakk>wadjust_on_left_moving_B m rs (c, Bk # list); hd c = Oc\<rbrakk>
    \<Longrightarrow> wadjust_on_left_moving_O m rs (tl c, Oc # Bk # list)"
  apply(auto simp: wadjust_on_left_moving_O.simps wadjust_on_left_moving_B.simps)
  by (metis cell.distinct(1) empty_replicate hd_append hd_replicate list.sel(3) self_append_conv2)

lemma wadjust_on_left_moving_B_drop[simp]: "wadjust_on_left_moving  m rs (c, Bk # list) \<Longrightarrow>  
                  wadjust_on_left_moving m rs (tl c, hd c # Bk # list)"
  by(cases "hd c", auto simp:wadjust_on_left_moving.simps wadjust_on_left_moving_B_Bk_drop_one
      wadjust_on_left_moving_B_Bk_drop_Oc)

lemma wadjust_goon_left_moving_O_no_Bk[simp]: "wadjust_goon_left_moving_O m rs (c, Bk # list) = False"
  by (auto simp add: wadjust_goon_left_moving_O.simps)

lemma wadjust_backto_standard_pos_via_left_Bk[simp]:
  "wadjust_goon_left_moving m rs (c, Bk # list) \<Longrightarrow>
  wadjust_backto_standard_pos m rs (tl c, hd c # Bk # list)"
  by(case_tac "hd c", simp_all add: wadjust_backto_standard_pos.simps wadjust_goon_left_moving.simps
      wadjust_goon_left_moving_B.simps wadjust_backto_standard_pos_O.simps)

lemma wadjust_loop_right_move_Oc[simp]:
  "wadjust_loop_start m rs (c, Oc # list) \<Longrightarrow> wadjust_loop_right_move m rs (Oc # c, list)"
  apply(auto simp add: wadjust_loop_start.simps wadjust_loop_right_move.simps
      simp del:split_head_repeat)
  apply(rename_tac ln rn ml mr)
  apply(rule_tac x = ml in exI, rule_tac x = mr in exI, 
      rule_tac x = 0 in exI, simp)
  apply(rule_tac x = "Suc ln" in exI, simp add: exp_ind del: replicate_Suc)
  done

lemma wadjust_loop_check_Oc[simp]:
  assumes "wadjust_loop_right_move m rs (c, Oc # list)" 
  shows "wadjust_loop_check m rs (Oc # c, list)"
proof -
  from assms obtain ml mr nl nr rn
    where "c = Bk \<up> nl @ Oc # Oc \<up> ml @ Bk # Oc \<up> m @ [Oc]"
      "Oc # list = Bk \<up> nr @ Oc \<up> mr @ Bk \<up> rn"
      "ml + mr = Suc (Suc rs)" "0 < mr" "0 < nl + nr"
    unfolding wadjust_loop_right_move.simps exp_ind 
      wadjust_loop_check.simps by auto
  hence "\<exists>ln. Oc # c = Oc # Bk \<up> ln @ Bk # Oc # Oc \<up> ml @ Bk # Oc \<up> Suc m"
    "\<exists>rn. list = Oc \<up> (mr - 1) @ Bk \<up> rn" "ml + (mr - 1) = Suc rs"
    by(cases nl;cases nr;cases mr;force simp add: wadjust_loop_right_move.simps exp_ind 
        wadjust_loop_check.simps replicate_append_same)+
  thus ?thesis unfolding wadjust_loop_check.simps by auto
qed

lemma wadjust_loop_erase_move_Oc[simp]: "wadjust_loop_check m rs (c, Oc # list) \<Longrightarrow> 
               wadjust_loop_erase m rs (tl c, hd c # Oc # list)"
  apply(simp only: wadjust_loop_check.simps wadjust_loop_erase.simps)
  apply(erule_tac exE)+
  using Cons_replicate_eq by fastforce

lemma wadjust_loop_on_move_no_Oc[simp]:
  "wadjust_loop_on_left_moving_B m rs (c, Oc # list) = False"
  "wadjust_loop_right_move2 m rs (c, Oc # list) = False"
  "wadjust_loop_on_left_moving m rs (c, Oc # list)
           \<Longrightarrow> wadjust_loop_right_move2 m rs (Oc # c, list)"
  "wadjust_on_left_moving_B m rs (c, Oc # list) = False"
  "wadjust_loop_erase m rs (c, Oc # list) \<Longrightarrow> 
                wadjust_loop_erase m rs (c, Bk # list)"
  by(auto simp: wadjust_loop_on_left_moving_B.simps wadjust_loop_on_left_moving_O.simps
      wadjust_loop_right_move2.simps replicate_app_Cons_same wadjust_loop_on_left_moving.simps
      wadjust_on_left_moving_B.simps wadjust_loop_erase.simps)

lemma wadjust_goon_left_moving_B_Bk_Oc: "\<lbrakk>wadjust_on_left_moving_O m rs (c, Oc # list); hd c = Bk\<rbrakk> \<Longrightarrow> 
         wadjust_goon_left_moving_B m rs (tl c, Bk # Oc # list)"
  apply(auto simp: wadjust_on_left_moving_O.simps 
      wadjust_goon_left_moving_B.simps )
  done

lemma wadjust_goon_left_moving_O_Oc_Oc: "\<lbrakk>wadjust_on_left_moving_O m rs (c, Oc # list); hd c = Oc\<rbrakk>
    \<Longrightarrow> wadjust_goon_left_moving_O m rs (tl c, Oc # Oc # list)"
  apply(auto simp: wadjust_on_left_moving_O.simps 
      wadjust_goon_left_moving_O.simps )
  apply(auto simp:  numeral_2_eq_2)
  done


lemma wadjust_goon_left_moving_Oc[simp]: "wadjust_on_left_moving m rs (c, Oc # list) \<Longrightarrow> 
              wadjust_goon_left_moving m rs (tl c, hd c # Oc # list)"
  by(cases "hd c"; force simp: wadjust_on_left_moving.simps wadjust_goon_left_moving.simps
      wadjust_goon_left_moving_B_Bk_Oc wadjust_goon_left_moving_O_Oc_Oc)+

lemma left_moving_Bk_Oc[simp]: "\<lbrakk>wadjust_goon_left_moving_O m rs (c, Oc # list); hd c = Bk\<rbrakk> 
               \<Longrightarrow> wadjust_goon_left_moving_B m rs (tl c, Bk # Oc # list)"
  apply(auto simp: wadjust_goon_left_moving_O.simps wadjust_goon_left_moving_B.simps hd_append
      dest!: gr0_implies_Suc)
   apply (metis cell.distinct(1) empty_replicate hd_replicate list.sel(3) self_append_conv2)
  by (metis add_cancel_right_left cell.distinct(1) hd_replicate replicate_Suc_iff_anywhere)

lemma  left_moving_Oc_Oc[simp]: "\<lbrakk>wadjust_goon_left_moving_O m rs (c, Oc # list); hd c = Oc\<rbrakk> \<Longrightarrow> 
  wadjust_goon_left_moving_O m rs (tl c, Oc # Oc # list)"
  apply(auto simp: wadjust_goon_left_moving_O.simps wadjust_goon_left_moving_B.simps)
  apply(rename_tac mlx mrx rnx)
  apply(rule_tac x = "mlx - 1" in exI, simp)
  apply(case_tac mlx, simp_all add: )
  apply(rule_tac x = "Suc mrx" in exI, auto simp: )
  done

lemma wadjust_goon_left_moving_B_no_Oc[simp]:
  "wadjust_goon_left_moving_B m rs (c, Oc # list) = False"
  apply(auto simp: wadjust_goon_left_moving_B.simps)
  done

lemma wadjust_goon_left_moving_Oc_move[simp]: "wadjust_goon_left_moving m rs (c, Oc # list) \<Longrightarrow> 
  wadjust_goon_left_moving m rs (tl c, hd c # Oc # list)"
  by(cases "hd c",auto simp: wadjust_goon_left_moving.simps)

lemma wadjust_backto_standard_pos_B_no_Oc[simp]:
  "wadjust_backto_standard_pos_B m rs (c, Oc # list) = False"
  apply(simp add: wadjust_backto_standard_pos_B.simps)
  done

lemma wadjust_backto_standard_pos_O_no_Bk[simp]:
  "wadjust_backto_standard_pos_O m rs (c, Bk # xs) = False"
  by(simp add: wadjust_backto_standard_pos_O.simps)

lemma wadjust_backto_standard_pos_B_Bk_Oc[simp]:
  "wadjust_backto_standard_pos_O m rs ([], Oc # list) \<Longrightarrow> 
  wadjust_backto_standard_pos_B m rs ([], Bk # Oc # list)"
  apply(auto simp: wadjust_backto_standard_pos_O.simps
      wadjust_backto_standard_pos_B.simps)
  done

lemma wadjust_backto_standard_pos_B_Bk_Oc_via_O[simp]: 
  "\<lbrakk>wadjust_backto_standard_pos_O m rs (c, Oc # list); c \<noteq> []; hd c = Bk\<rbrakk>
  \<Longrightarrow> wadjust_backto_standard_pos_B m rs (tl c, Bk # Oc # list)"
  apply(simp add:wadjust_backto_standard_pos_O.simps 
      wadjust_backto_standard_pos_B.simps, auto)
  done 

lemma wadjust_backto_standard_pos_B_Oc_Oc_via_O[simp]: "\<lbrakk>wadjust_backto_standard_pos_O m rs (c, Oc # list); c \<noteq> []; hd c = Oc\<rbrakk>
          \<Longrightarrow>  wadjust_backto_standard_pos_O m rs (tl c, Oc # Oc # list)"
  apply(simp add: wadjust_backto_standard_pos_O.simps, auto)
  by force

lemma wadjust_backto_standard_pos_cases[simp]: "wadjust_backto_standard_pos m rs (c, Oc # list)
  \<Longrightarrow> (c = [] \<longrightarrow> wadjust_backto_standard_pos m rs ([], Bk # Oc # list)) \<and> 
 (c \<noteq> [] \<longrightarrow> wadjust_backto_standard_pos m rs (tl c, hd c # Oc # list))"
  apply(auto simp: wadjust_backto_standard_pos.simps)
  apply(case_tac "hd c", simp_all)
  done

lemma wadjust_loop_right_move_nonempty_snd[simp]: "wadjust_loop_right_move m rs (c, []) = False"
proof -
  {fix nl ml mr rn nr
    have "(c = Bk \<up> nl @ Oc # Oc \<up> ml @ Bk # Oc \<up> Suc m \<and>
        [] = Bk \<up> nr @ Oc \<up> mr @ Bk \<up> rn \<and> ml + mr = Suc (Suc rs) \<and> 0 < mr \<and> 0 < nl + nr) =
    False" by auto
  } note t=this
  thus ?thesis unfolding wadjust_loop_right_move.simps t by blast
qed

lemma wadjust_loop_erase_nonempty_snd[simp]: "wadjust_loop_erase m rs (c, []) = False"
  apply(simp only: wadjust_loop_erase.simps, auto)
  done

lemma wadjust_loop_erase_cases2[simp]: "\<lbrakk>Suc (Suc rs) = a;  wadjust_loop_erase m rs (c, Bk # list)\<rbrakk>
  \<Longrightarrow> a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev (tl c) @ hd c # Bk # list))))
  < a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Bk # list)))) \<or>
  a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev (tl c) @ hd c # Bk # list)))) =
  a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Bk # list))))"
  apply(simp only: wadjust_loop_erase.simps)
  apply(rule_tac disjI2)
  apply(case_tac c, simp, simp)
  done

lemma dropWhile_exp1: "dropWhile (\<lambda>a. a = Oc) (Oc\<up>(n) @ xs) = dropWhile (\<lambda>a. a = Oc) xs"
  apply(induct n, simp_all add: )
  done
lemma takeWhile_exp1: "takeWhile (\<lambda>a. a = Oc) (Oc\<up>(n) @ xs) = Oc\<up>(n) @ takeWhile (\<lambda>a. a = Oc) xs"
  apply(induct n, simp_all add: )
  done

lemma wadjust_correctness_helper_1:
  assumes "Suc (Suc rs) = a" " wadjust_loop_right_move2 m rs (c, Bk # list)"
  shows "a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Oc # list))))
                 < a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Bk # list))))"
proof -
  have "ml + mr = Suc rs \<Longrightarrow> 0 < mr \<Longrightarrow>
       rs - (ml + length (takeWhile (\<lambda>a. a = Oc) list))
       < Suc rs -
         (ml +
          length
           (takeWhile (\<lambda>a. a = Oc)
             (Bk \<up> ln @ Bk # Bk # Oc \<up> mr @ Bk \<up> rn))) "
    for ml mr ln rn
    by(cases ln, auto)
  thus ?thesis using assms
    by (auto simp: wadjust_loop_right_move2.simps dropWhile_exp1 takeWhile_exp1)
qed

lemma wadjust_correctness_helper_2:
  "\<lbrakk>Suc (Suc rs) = a;  wadjust_loop_on_left_moving m rs (c, Bk # list)\<rbrakk>
  \<Longrightarrow> a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev (tl c) @ hd c # Bk # list))))
  < a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Bk # list)))) \<or>
  a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev (tl c) @ hd c # Bk # list)))) =
  a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Bk # list))))"
  apply(subgoal_tac "c \<noteq> []")
   apply(case_tac c, simp_all)
  done

lemma wadjust_loop_check_empty_false[simp]: "wadjust_loop_check m rs ([], b) = False"
  apply(simp add: wadjust_loop_check.simps)
  done

lemma wadjust_loop_check_cases: "\<lbrakk>Suc (Suc rs) = a;  wadjust_loop_check m rs (c, Oc # list)\<rbrakk>
  \<Longrightarrow> a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev (tl c) @ hd c # Oc # list))))
  < a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Oc # list)))) \<or>
  a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev (tl c) @ hd c # Oc # list)))) =
  a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Oc # list))))"
  apply(case_tac "c", simp_all)
  done

lemma wadjust_loop_erase_cases_or: 
  "\<lbrakk>Suc (Suc rs) = a;  wadjust_loop_erase m rs (c, Oc # list)\<rbrakk>
  \<Longrightarrow> a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Bk # list))))
  < a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Oc # list)))) \<or>
  a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Bk # list)))) =
  a - length (takeWhile (\<lambda>a. a = Oc) (tl (dropWhile (\<lambda>a. a = Oc) (rev c @ Oc # list))))"
  apply(simp add: wadjust_loop_erase.simps)
  apply(rule_tac disjI2)
  apply(auto)
  apply(simp add: dropWhile_exp1 takeWhile_exp1)
  done

lemmas wadjust_correctness_helpers = wadjust_correctness_helper_2 wadjust_correctness_helper_1 wadjust_loop_erase_cases_or wadjust_loop_check_cases

declare numeral_2_eq_2[simp del]

lemma wadjust_start_Oc[simp]: "wadjust_start m rs (c, Bk # list)
       \<Longrightarrow> wadjust_start m rs (c, Oc # list)"
  apply(auto simp: wadjust_start.simps)
  done

lemma wadjust_stop_Bk[simp]: "wadjust_backto_standard_pos m rs (c, Bk # list)
       \<Longrightarrow> wadjust_stop m rs (Bk # c, list)"
  apply(auto simp: wadjust_backto_standard_pos.simps 
      wadjust_stop.simps wadjust_backto_standard_pos_B.simps)
  done

lemma wadjust_loop_start_Oc[simp]:
  assumes "wadjust_start m rs (c, Oc # list)"
  shows "wadjust_loop_start m rs (Oc # c, list)"
proof -
  from assms[unfolded wadjust_start.simps] obtain ln rn where
    "c = Bk # Oc # Oc \<up> m" "list = Oc # Bk \<up> ln @ Bk # Oc # Oc \<up> rs @ Bk \<up> rn"
    by(auto)
  hence "Oc # c = Oc \<up> 1 @ Bk # Oc \<up> Suc m \<and>
       list = Oc # Bk \<up> ln @ Bk # Oc \<up>Suc rs @ Bk \<up> rn \<and> 1 + (Suc rs) = Suc (Suc rs) \<and> 0 < Suc rs"
    by auto
  thus ?thesis unfolding wadjust_loop_start.simps by blast
qed

lemma erase2_Bk_if_Oc[simp]:" wadjust_erase2 m rs (c, Oc # list)
       \<Longrightarrow> wadjust_erase2 m rs (c, Bk # list)"
  apply(auto simp: wadjust_erase2.simps)
  done

lemma wadjust_loop_right_move_Bk[simp]: "wadjust_loop_right_move m rs (c, Bk # list)
    \<Longrightarrow> wadjust_loop_right_move m rs (Bk # c, list)"
  apply(simp only: wadjust_loop_right_move.simps)
  apply(erule_tac exE)+
  apply auto
   apply (metis cell.distinct(1) empty_replicate hd_append hd_replicate less_SucI
      list.sel(1) list.sel(3) neq0_conv replicate_Suc_iff_anywhere tl_append2 tl_replicate)+
  done

lemma wadjust_correctness:
  shows "let P = (\<lambda> (len, st, l, r). st = 0) in 
  let Q = (\<lambda> (len, st, l, r). wadjust_inv st m rs (l, r)) in 
  let f = (\<lambda> stp. (Suc (Suc rs),  steps0 (Suc 0, Bk # Oc\<up>(Suc m), 
                Bk # Oc # Bk\<up>(ln) @ Bk #  Oc\<up>(Suc rs) @ Bk\<up>(rn)) t_wcode_adjust stp)) in
    \<exists> n .P (f n) \<and> Q (f n)"
proof -
  let ?P = "(\<lambda> (len, st, l, r). st = 0)"
  let ?Q = "\<lambda> (len, st, l, r). wadjust_inv st m rs (l, r)"
  let ?f = "\<lambda> stp. (Suc (Suc rs),  steps0 (Suc 0, Bk # Oc\<up>(Suc m), 
                Bk # Oc # Bk\<up>(ln) @ Bk # Oc\<up>(Suc rs) @ Bk\<up>(rn)) t_wcode_adjust stp)"
  have "\<exists> n. ?P (?f n) \<and> ?Q (?f n)"
  proof(rule_tac halt_lemma2)
    show "wf wadjust_le" by auto
  next
    { fix n assume a:"\<not> ?P (?f n) \<and> ?Q (?f n)"
      have "?Q (?f (Suc n)) \<and> (?f (Suc n), ?f n) \<in> wadjust_le"
      proof(cases "?f n")
        case (fields a b c d)
        then show ?thesis proof(cases d)
          case Nil
          then show ?thesis using a fields apply(simp add: step.simps)
            apply(simp_all only: wadjust_inv.simps split: if_splits)
                        apply(simp_all add: wadjust_inv.simps wadjust_le_def
                wadjust_correctness_helpers
                Abacus.lex_triple_def Abacus.lex_pair_def lex_square_def  split: if_splits).
        next
          case (Cons aa list)
          then show ?thesis using a fields Nil Cons
            apply((case_tac aa); simp add: step.simps)
             apply(simp_all only: wadjust_inv.simps split: if_splits)
                                apply(simp_all)
                               apply(simp_all add: wadjust_inv.simps wadjust_le_def
                wadjust_correctness_helpers
                Abacus.lex_triple_def Abacus.lex_pair_def lex_square_def  split: if_splits).
        qed
      qed
    }
    thus "\<forall> n. \<not> ?P (?f n) \<and> ?Q (?f n) \<longrightarrow> 
                 ?Q (?f (Suc n)) \<and> (?f (Suc n), ?f n) \<in> wadjust_le" by auto
  next
    show "?Q (?f 0)" by(auto simp add: steps.simps wadjust_inv.simps wadjust_start.simps)
  next
    show "\<not> ?P (?f 0)" by (simp add: steps.simps)
  qed
  thus"?thesis" by simp
qed

lemma tm_wf_t_wcode_adjust[intro]: "tm_wf (t_wcode_adjust, 0)"
  by(auto simp: t_wcode_adjust_def tm_wf.simps)

lemma bl_bin_nonzero[simp]: "args \<noteq> [] \<Longrightarrow> bl_bin (<args::nat list>) > 0"
  by(cases args)
    (auto simp: tape_of_nl_cons bl_bin.simps)

lemma wcode_lemma_pre':
  "args \<noteq> [] \<Longrightarrow> 
  \<exists> stp rn. steps0 (Suc 0, [], <m # args>) 
              ((t_wcode_prepare |+| t_wcode_main) |+| t_wcode_adjust) stp
  = (0,  [Bk],  Oc\<up>(Suc m) @ Bk # Oc\<up>(Suc (bl_bin (<args>))) @ Bk\<up>(rn))" 
proof -
  let ?P1 = "\<lambda> (l, r). l = [] \<and> r = <m # args>"
  let ?Q1 = "\<lambda>(l, r). l = Bk # Oc\<up>(Suc m) \<and>
    (\<exists>ln rn. r = Bk # Oc # Bk\<up>(ln) @ Bk # Bk # Oc\<up>(bl_bin (<args>)) @ Bk\<up>(rn))"
  let ?P2 = ?Q1
  let ?Q2 = "\<lambda> (l, r). (wadjust_stop m (bl_bin (<args>) - 1) (l, r))"
  let ?P3 = "\<lambda> tp. False"
  assume h: "args \<noteq> []"
  hence a: "bl_bin (<args>) > 0"
    using h by simp
  hence "{?P1} (t_wcode_prepare |+| t_wcode_main) |+| t_wcode_adjust {?Q2}"
  proof(rule_tac Hoare_plus_halt)
  next
    show "tm_wf (t_wcode_prepare |+| t_wcode_main, 0)"
      by(rule_tac tm_comp_wf, auto)
  next
    show "{?P1} t_wcode_prepare |+| t_wcode_main {?Q1}"
    proof(rule_tac Hoare_haltI, auto)
      show 
        "\<exists>n. is_final (steps0 (Suc 0, [], <m # args>) (t_wcode_prepare |+| t_wcode_main) n) \<and>
        (\<lambda>(l, r). l = Bk # Oc # Oc \<up> m \<and>
        (\<exists>ln rn. r = Bk # Oc # Bk \<up> ln @ Bk # Bk # Oc \<up> bl_bin (<args>) @ Bk \<up> rn))
        holds_for steps0 (Suc 0, [], <m # args>) (t_wcode_prepare |+| t_wcode_main) n"
        using h prepare_mainpart_lemma[of args m]
        apply(auto) apply(rename_tac stp ln rn)
        apply(rule_tac x = stp in exI, simp)
        apply(rule_tac x = ln in exI, auto)
        done
    qed
  next
    show "{?P2} t_wcode_adjust {?Q2}"
    proof(rule_tac Hoare_haltI, auto del: replicate_Suc)
      fix ln rn
      obtain n a b where "steps0
        (Suc 0, Bk # Oc \<up> m @ [Oc],
         Bk # Oc # Bk \<up> ln @ Bk # Bk # Oc \<up> (bl_bin (<args>) - Suc 0) @ Oc # Bk \<up> rn)
        t_wcode_adjust n = (0, a, b)"
        "wadjust_inv 0 m (bl_bin (<args>) - Suc 0) (a, b)"
        using wadjust_correctness[of m "bl_bin (<args>) - 1" "Suc ln" rn,unfolded Let_def]
        by(simp del: replicate_Suc add: replicate_Suc[THEN sym] exp_ind, auto)
      thus "\<exists>n. is_final (steps0 (Suc 0, Bk # Oc # Oc \<up> m, 
        Bk # Oc # Bk \<up> ln @ Bk # Bk # Oc \<up> bl_bin (<args>) @ Bk \<up> rn) t_wcode_adjust n) \<and>
        wadjust_stop m (bl_bin (<args>) - Suc 0) holds_for steps0
        (Suc 0, Bk # Oc # Oc \<up> m, Bk # Oc # Bk \<up> ln @ Bk # Bk # Oc \<up> bl_bin (<args>) @ Bk \<up> rn) t_wcode_adjust n"
        apply(rule_tac x = n in exI)
        using a
        apply(case_tac "bl_bin (<args>)", simp, simp del: replicate_Suc add: exp_ind wadjust_inv.simps)
        by (simp add: replicate_append_same)
    qed
  qed
  thus "?thesis"
    apply(simp add: Hoare_halt_def, auto)
    apply(rename_tac n)
    apply(case_tac "(steps0 (Suc 0, [], <(m::nat) # args>) 
      ((t_wcode_prepare |+| t_wcode_main) |+| t_wcode_adjust) n)")
    apply(rule_tac x = n in exI, auto simp: wadjust_stop.simps)
    using a
    apply(case_tac "bl_bin (<args>)", simp_all)
    done
qed

text \<open>
  The initialization TM \<open>t_wcode\<close>.
\<close>
definition t_wcode :: "instr list"
  where
    "t_wcode = (t_wcode_prepare |+| t_wcode_main) |+| t_wcode_adjust        "

text \<open>
  The correctness of \<open>t_wcode\<close>.
\<close>

lemma wcode_lemma_1:
  "args \<noteq> [] \<Longrightarrow> 
  \<exists> stp ln rn. steps0 (Suc 0, [], <m # args>)  (t_wcode) stp = 
              (0,  [Bk],  Oc\<up>(Suc m) @ Bk # Oc\<up>(Suc (bl_bin (<args>))) @ Bk\<up>(rn))"
  apply(simp add: wcode_lemma_pre' t_wcode_def del: replicate_Suc)
  done

lemma wcode_lemma: 
  "args \<noteq> [] \<Longrightarrow> 
  \<exists> stp ln rn. steps0 (Suc 0, [], <m # args>)  (t_wcode) stp = 
              (0,  [Bk],  <[m ,bl_bin (<args>)]> @ Bk\<up>(rn))"
  using wcode_lemma_1[of args m]
  apply(simp add: t_wcode_def tape_of_list_def tape_of_nat_def)
  done

section \<open>The universal TM\<close>

text \<open>
  This section gives the explicit construction of {\em Universal Turing Machine}, defined as \<open>UTM\<close> and proves its 
  correctness. It is pretty easy by composing the partial results we have got so far.
\<close>


definition UTM :: "instr list"
  where
    "UTM = (let (aprog, rs_pos, a_md) = rec_ci rec_F in 
          let abc_F = aprog [+] dummy_abc (Suc (Suc 0)) in 
          (t_wcode |+| (tm_of abc_F @ shift (mopup (Suc (Suc 0))) (length (tm_of abc_F) div 2))))"

definition F_aprog :: "abc_prog"
  where
    "F_aprog \<equiv> (let (aprog, rs_pos, a_md) = rec_ci rec_F in 
                       aprog [+] dummy_abc (Suc (Suc 0)))"

definition F_tprog :: "instr list"
  where
    "F_tprog = tm_of (F_aprog)"

definition t_utm :: "instr list"
  where
    "t_utm \<equiv>
     F_tprog @ shift (mopup (Suc (Suc 0))) (length F_tprog div 2)"

definition UTM_pre :: "instr list"
  where
    "UTM_pre = t_wcode |+| t_utm"

lemma tinres_step1: 
  assumes "tinres l l'" "step (ss, l, r) (t, 0) = (sa, la, ra)" 
    "step (ss, l', r) (t, 0) = (sb, lb, rb)"
  shows "tinres la lb \<and> ra = rb \<and> sa = sb"
proof(cases "r")
  case Nil
  then show ?thesis using assms
    by (cases "(fetch t ss Bk)";cases "fst (fetch t ss Bk)";auto simp:step.simps split:if_splits)
next
  case (Cons a list)
  then show ?thesis using assms
    by (cases "(fetch t ss a)";cases "fst (fetch t ss a)";auto simp:step.simps split:if_splits)
qed

lemma tinres_steps1: 
  "\<lbrakk>tinres l l'; steps (ss, l, r) (t, 0) stp = (sa, la, ra); 
                 steps (ss, l', r) (t, 0) stp = (sb, lb, rb)\<rbrakk>
    \<Longrightarrow> tinres la lb \<and> ra = rb \<and> sa = sb"
proof (induct stp arbitrary: sa la ra sb lb rb)
  case (Suc stp)
  then show ?case apply simp 
    apply(case_tac "(steps (ss, l, r) (t, 0) stp)")
    apply(case_tac "(steps (ss, l', r) (t, 0) stp)")
  proof -
    fix stp sa la ra sb lb rb a b c aa ba ca
    assume ind: "\<And>sa la ra sb lb rb. \<lbrakk>steps (ss, l, r) (t, 0) stp = (sa, (la::cell list), ra); 
          steps (ss, l', r) (t, 0) stp = (sb, lb, rb)\<rbrakk> \<Longrightarrow> tinres la lb \<and> ra = rb \<and> sa = sb"
      and h: " tinres l l'" "step (steps (ss, l, r) (t, 0) stp) (t, 0) = (sa, la, ra)"
      "step (steps (ss, l', r) (t, 0) stp) (t, 0) = (sb, lb, rb)" "steps (ss, l, r) (t, 0) stp = (a, b, c)" 
      "steps (ss, l', r) (t, 0) stp = (aa, ba, ca)"
    have "tinres b ba \<and> c = ca \<and> a = aa"
      using ind h by metis
    thus "tinres la lb \<and> ra = rb \<and> sa = sb"
      using tinres_step1 h by metis
  qed
qed (simp add: steps.simps)

lemma tinres_some_exp[simp]: 
  "tinres (Bk \<up> m @ [Bk, Bk]) la \<Longrightarrow> \<exists>m. la = Bk \<up> m" unfolding tinres_def
proof -
  let ?c1 = "\<lambda> n. Bk \<up> m @ [Bk, Bk] = la @ Bk \<up> n"
  let ?c2 = "\<lambda> n. la = (Bk \<up> m @ [Bk, Bk]) @ Bk \<up> n"
  assume "\<exists>n. ?c1 n \<or> ?c2 n"
  then obtain n where "?c1 n \<or> ?c2 n" by auto
  then consider "?c1 n" | "?c2 n" by blast
  thus ?thesis proof(cases)
    case 1
    hence "Bk \<up> Suc (Suc m) = la @ Bk \<up> n"
      by (metis exp_ind append_Cons append_eq_append_conv2 self_append_conv2)
    hence "la = Bk \<up> (Suc (Suc m) - n)"
      by (metis replicate_add append_eq_append_conv diff_add_inverse2 length_append length_replicate)
    then show ?thesis by auto
  next
    case 2
    hence "la = Bk \<up> (m + Suc (Suc n))"
      by (metis append_Cons append_eq_append_conv2 replicate_Suc replicate_add self_append_conv2)
    then show ?thesis by blast
  qed
qed

lemma t_utm_halt_eq: 
  assumes tm_wf: "tm_wf (tp, 0)"
    and exec: "steps0 (Suc 0, Bk\<up>(l), <lm::nat list>) tp stp = (0, Bk\<up>(m), Oc\<up>(rs)@Bk\<up>(n))"
    and resutl: "0 < rs"
  shows "\<exists>stp m n. steps0 (Suc 0, [Bk], <[code tp, bl2wc (<lm>)]> @ Bk\<up>(i)) t_utm stp = 
                                                (0, Bk\<up>(m), Oc\<up>(rs) @ Bk\<up>(n))"
proof -
  obtain ap arity fp where a: "rec_ci rec_F = (ap, arity, fp)"
    by (metis prod_cases3) 
  moreover have b: "rec_exec rec_F [code tp, (bl2wc (<lm>))] = (rs - Suc 0)"
    using assms
    apply(rule_tac F_correct, simp_all)
    done 
  have "\<exists> stp m l. steps0 (Suc 0, Bk # Bk # [], <[code tp, bl2wc (<lm>)]> @ Bk\<up>i)
    (F_tprog @ shift (mopup (length [code tp, bl2wc (<lm>)])) (length F_tprog div 2)) stp
    = (0, Bk\<up>m @ Bk # Bk # [], Oc\<up>Suc (rec_exec rec_F [code tp, (bl2wc (<lm>))]) @ Bk\<up>l)"  
  proof(rule_tac recursive_compile_to_tm_correct1)
    show "rec_ci rec_F = (ap, arity, fp)" using a by simp
  next
    show "terminate rec_F [code tp, bl2wc (<lm>)]"
      using assms
      by(rule_tac terminate_F, simp_all)
  next
    show "F_tprog = tm_of (ap [+] dummy_abc (length [code tp, bl2wc (<lm>)]))"
      using a
      apply(simp add: F_tprog_def F_aprog_def numeral_2_eq_2)
      done
  qed
  then obtain stp m l where 
    "steps0 (Suc 0, Bk # Bk # [], <[code tp, bl2wc (<lm>)]> @ Bk\<up>i)
    (F_tprog @ shift (mopup (length [code tp, (bl2wc (<lm>))])) (length F_tprog div 2)) stp
    = (0, Bk\<up>m @ Bk # Bk # [], Oc\<up>Suc (rec_exec rec_F [code tp, (bl2wc (<lm>))]) @ Bk\<up>l)" by blast
  hence "\<exists> m. steps0 (Suc 0, [Bk], <[code tp, bl2wc (<lm>)]> @ Bk\<up>i)
    (F_tprog @ shift (mopup 2) (length F_tprog div 2)) stp
    = (0, Bk\<up>m, Oc\<up>Suc (rs - 1) @ Bk\<up>l)"
  proof -
    assume g: "steps0 (Suc 0, [Bk, Bk], <[code tp, bl2wc (<lm>)]> @ Bk \<up> i)
      (F_tprog @ shift (mopup (length [code tp, bl2wc (<lm>)])) (length F_tprog div 2)) stp =
      (0, Bk \<up> m @ [Bk, Bk], Oc \<up> Suc ((rec_exec rec_F [code tp, bl2wc (<lm>)])) @ Bk \<up> l)"
    moreover have "tinres [Bk, Bk] [Bk]"
      apply(auto simp: tinres_def)
      done
    moreover obtain sa la ra where "steps0 (Suc 0, [Bk], <[code tp, bl2wc (<lm>)]> @ Bk\<up>i)
    (F_tprog @ shift (mopup 2) (length F_tprog div 2)) stp = (sa, la, ra)"
      apply(case_tac "steps0 (Suc 0, [Bk], <[code tp, bl2wc (<lm>)]> @ Bk\<up>i)
    (F_tprog @ shift (mopup 2) (length F_tprog div 2)) stp", auto)
      done
    ultimately show "?thesis"
      using b
      apply(drule_tac la = "Bk\<up>m @ [Bk, Bk]" in tinres_steps1, auto simp: numeral_2_eq_2)
      done
  qed
  thus "?thesis"
    apply(auto)
    apply(rule_tac x = stp in exI, simp add: t_utm_def)
    using assms
    apply(case_tac rs, simp_all add: numeral_2_eq_2)
    done
qed

lemma tm_wf_t_wcode[intro]: "tm_wf (t_wcode, 0)"
  apply(simp add: t_wcode_def)
  apply(rule_tac tm_comp_wf)
   apply(rule_tac tm_comp_wf, auto)
  done

lemma UTM_halt_lemma_pre: 
  assumes wf_tm: "tm_wf (tp, 0)"
    and result: "0 < rs"
    and args: "args \<noteq> []"
    and exec: "steps0 (Suc 0, Bk\<up>(i), <args::nat list>) tp stp = (0, Bk\<up>(m), Oc\<up>(rs)@Bk\<up>(k))"
  shows "\<exists>stp m n. steps0 (Suc 0, [], <code tp # args>) UTM_pre stp = 
                                                (0, Bk\<up>(m), Oc\<up>(rs) @ Bk\<up>(n))"
proof -
  let ?Q2 = "\<lambda> (l, r). (\<exists> ln rn. l = Bk\<up>(ln) \<and> r = Oc\<up>(rs) @ Bk\<up>(rn))"
  let ?P1 = "\<lambda> (l, r). l = [] \<and> r = <code tp # args>"
  let ?Q1 = "\<lambda> (l, r). (l = [Bk] \<and>
    (\<exists> rn. r = Oc\<up>(Suc (code tp)) @ Bk # Oc\<up>(Suc (bl_bin (<args>))) @ Bk\<up>(rn)))"
  let ?P2 = ?Q1
  let ?P3 = "\<lambda> (l, r). False"
  have "{?P1} (t_wcode |+| t_utm) {?Q2}"
  proof(rule_tac Hoare_plus_halt)
    show "tm_wf (t_wcode, 0)" by auto
  next
    show "{?P1} t_wcode {?Q1}"
      apply(rule_tac Hoare_haltI, auto)
      using wcode_lemma_1[of args "code tp"] args
      apply(auto)
      by (metis (mono_tags, lifting) holds_for.simps is_finalI old.prod.case)
  next
    show "{?P2} t_utm {?Q2}"
    proof(rule_tac Hoare_haltI, auto)
      fix rn
      show "\<exists>n. is_final (steps0 (Suc 0, [Bk], Oc # Oc \<up> code tp @ Bk # Oc # Oc \<up> bl_bin (<args>) @ Bk \<up> rn) t_utm n) \<and>
        (\<lambda>(l, r). (\<exists>ln. l = Bk \<up> ln) \<and>
        (\<exists>rn. r = Oc \<up> rs @ Bk \<up> rn)) holds_for steps0 (Suc 0, [Bk],
        Oc # Oc \<up> code tp @ Bk # Oc # Oc \<up> bl_bin (<args>) @ Bk \<up> rn) t_utm n"
        using t_utm_halt_eq[of tp i "args" stp m rs k rn] assms
        apply(auto simp: bin_wc_eq tape_of_list_def tape_of_nat_def)
        apply(rename_tac stpa) apply(rule_tac x = stpa in exI, simp)
        done
    qed
  qed
  thus "?thesis"
    apply(auto simp: Hoare_halt_def UTM_pre_def)
    apply(case_tac "steps0 (Suc 0, [], <code tp # args>) (t_wcode |+| t_utm) n",simp)
    by auto
qed

text \<open>
  The correctness of \<open>UTM\<close>, the halt case.
\<close>
lemma UTM_halt_lemma': 
  assumes tm_wf: "tm_wf (tp, 0)"
    and result: "0 < rs"
    and args: "args \<noteq> []"
    and exec: "steps0 (Suc 0, Bk\<up>(i), <args::nat list>) tp stp = (0, Bk\<up>(m), Oc\<up>(rs)@Bk\<up>(k))"
  shows "\<exists>stp m n. steps0 (Suc 0, [], <code tp # args>) UTM stp = 
                                                (0, Bk\<up>(m), Oc\<up>(rs) @ Bk\<up>(n))"
  using UTM_halt_lemma_pre[of tp rs args i stp m k] assms
  apply(simp add: UTM_pre_def t_utm_def UTM_def F_aprog_def F_tprog_def)
  apply(case_tac "rec_ci rec_F", simp)
  done

definition TSTD:: "config \<Rightarrow> bool"
  where
    "TSTD c = (let (st, l, r) = c in 
             st = 0 \<and> (\<exists> m. l = Bk\<up>(m)) \<and> (\<exists> rs n. r = Oc\<up>(Suc rs) @ Bk\<up>(n)))"

lemma nstd_case1: "0 < a \<Longrightarrow> NSTD (trpl_code (a, b, c))"
  by(simp add: NSTD.simps trpl_code.simps)

lemma nonzero_bl2wc[simp]: "\<forall>m. b \<noteq> Bk\<up>(m) \<Longrightarrow> 0 < bl2wc b"
proof -
  have "\<forall>m. b \<noteq> Bk \<up> m \<Longrightarrow> bl2wc b = 0 \<Longrightarrow> False" proof(induct b)
    case (Cons a b)
    then show ?case
      apply(simp add: bl2wc.simps, case_tac a, simp_all 
          add: bl2nat.simps bl2nat_double)
      apply(case_tac "\<exists> m. b = Bk\<up>(m)", erule exE)
       apply(metis append_Nil2 replicate_Suc_iff_anywhere) 
      by simp
  qed auto
  thus "\<forall>m. b \<noteq> Bk\<up>(m) \<Longrightarrow> 0 < bl2wc b" by auto
qed

lemma nstd_case2: "\<forall>m. b \<noteq> Bk\<up>(m) \<Longrightarrow> NSTD (trpl_code (a, b, c))"
  apply(simp add: NSTD.simps trpl_code.simps)
  done

lemma even_not_odd[elim]: "Suc (2 * x) = 2 * y \<Longrightarrow> RR"
proof(induct x arbitrary: y)
  case (Suc x) thus ?case by(cases y;auto)
qed auto

declare replicate_Suc[simp del]

lemma bl2nat_zero_eq[simp]: "(bl2nat c 0 = 0) = (\<exists>n. c = Bk\<up>(n))"
proof(induct c)
  case (Cons a c)
  then show ?case by (cases a;auto simp: bl2nat.simps bl2nat_double Cons_replicate_eq)
qed (auto simp: bl2nat.simps)

lemma bl2wc_exp_ex: 
  "\<lbrakk>Suc (bl2wc c) = 2 ^  m\<rbrakk> \<Longrightarrow> \<exists> rs n. c = Oc\<up>(rs) @ Bk\<up>(n)"
proof(induct c arbitrary: m)
  case (Cons a c m)
  { fix n
    have "Bk # Bk \<up> n = Oc \<up> 0 @ Bk \<up> Suc n" by (auto simp:replicate_Suc)
    hence "\<exists>rs na. Bk # Bk \<up> n = Oc \<up> rs @ Bk \<up> na" by blast
  }
  with Cons show ?case apply(cases a, auto)
     apply(case_tac m, simp_all add: bl2wc.simps, auto)
    apply(simp add: bl2wc.simps bl2nat.simps bl2nat_double Cons)
    apply(case_tac m, simp, simp add: bin_wc_eq bl2wc.simps twice_power )
    by (metis Cons.hyps Suc_pred bl2wc.simps neq0_conv power_not_zero
        replicate_Suc_iff_anywhere zero_neq_numeral)
qed (simp add: bl2wc.simps bl2nat.simps)

lemma lg_bin: 
  assumes "\<forall>rs n. c \<noteq> Oc\<up>(Suc rs) @ Bk\<up>(n)" 
    "bl2wc c = 2 ^ lg (Suc (bl2wc c)) 2 - Suc 0"
  shows "bl2wc c = 0"
proof -
  from assms obtain rs nat n where *:"2 ^ rs - Suc 0 = nat"
    "c = Oc \<up> rs @ Bk \<up> n" 
    using bl2wc_exp_ex[of c "lg (Suc (bl2wc c)) 2"]
    by(case_tac "(2::nat) ^ lg (Suc (bl2wc c)) 2", 
        simp, simp, erule_tac exE, erule_tac exE, simp)
  have r:"bl2wc (Oc \<up> rs) = nat" 
    by (metis "*"(1) bl2nat_exp_zero bl2wc.elims)
  hence "Suc (bl2wc c) = 2^rs" using *
    by(case_tac "(2::nat)^rs", auto)
  thus ?thesis using * assms(1)
    apply(drule_tac bl2wc_exp_ex, simp, erule_tac exE, erule_tac exE)
    by(case_tac rs, simp, simp)
qed

lemma nstd_case3: 
  "\<forall>rs n. c \<noteq> Oc\<up>(Suc rs) @ Bk\<up>(n) \<Longrightarrow>  NSTD (trpl_code (a, b, c))"
  apply(simp add: NSTD.simps trpl_code.simps)
  apply(auto)
  apply(drule_tac lg_bin, simp_all)
  done

lemma NSTD_1: "\<not> TSTD (a, b, c)
    \<Longrightarrow> rec_exec rec_NSTD [trpl_code (a, b, c)] = Suc 0"
  using NSTD_lemma1[of "trpl_code (a, b, c)"]
    NSTD_lemma2[of "trpl_code (a, b, c)"]
  apply(simp add: TSTD_def)
  apply(erule_tac disjE, erule_tac nstd_case1)
  apply(erule_tac disjE, erule_tac nstd_case2)
  apply(erule_tac nstd_case3)
  done

lemma nonstop_t_uhalt_eq:
  "\<lbrakk>tm_wf (tp, 0);
  steps0 (Suc 0, Bk\<up>(l), <lm>) tp stp = (a, b, c);
  \<not> TSTD (a, b, c)\<rbrakk>
  \<Longrightarrow> rec_exec rec_nonstop [code tp, bl2wc (<lm>), stp] = Suc 0"
  apply(simp add: rec_nonstop_def rec_exec.simps)
  apply(subgoal_tac 
      "rec_exec rec_conf [code tp, bl2wc (<lm>), stp] =
  trpl_code (a, b, c)", simp)
   apply(erule_tac NSTD_1)
  using rec_t_eq_steps[of tp l lm stp]
  apply(simp)
  done

lemma nonstop_true:
  "\<lbrakk>tm_wf (tp, 0);
  \<forall> stp. (\<not> TSTD (steps0 (Suc 0, Bk\<up>(l), <lm>) tp stp))\<rbrakk>
  \<Longrightarrow> \<forall>y. rec_exec rec_nonstop ([code tp, bl2wc (<lm>), y]) = (Suc 0)"
proof fix y
  assume a:"tm_wf0 tp" "\<forall>stp. \<not> TSTD (steps0 (Suc 0, Bk \<up> l, <lm>) tp stp)"
  hence "\<not> TSTD (steps0 (Suc 0, Bk \<up> l, <lm>) tp y)" by auto
  thus "rec_exec rec_nonstop [code tp, bl2wc (<lm>), y] = Suc 0"
    by (cases "steps0 (Suc 0, Bk\<up>(l), <lm>) tp y")
      (auto intro: nonstop_t_uhalt_eq[OF a(1)])
qed

lemma cn_arity:  "rec_ci (Cn n f gs) = (a, b, c) \<Longrightarrow> b = n"
  by(case_tac "rec_ci f", simp add: rec_ci.simps)

lemma mn_arity: "rec_ci (Mn n f) = (a, b, c) \<Longrightarrow> b = n"
  by(case_tac "rec_ci f", simp add: rec_ci.simps)

lemma F_aprog_uhalt: 
  assumes wf_tm: "tm_wf (tp,0)"
    and unhalt:  "\<forall> stp. (\<not> TSTD (steps0 (Suc 0, Bk\<up>(l), <lm>) tp stp))"
    and compile: "rec_ci rec_F = (F_ap, rs_pos, a_md)"
  shows "{\<lambda> nl. nl = [code tp, bl2wc (<lm>)] @ 0\<up>(a_md - rs_pos ) @ suflm} (F_ap) \<up>"
  using compile
proof(simp only: rec_F_def)
  assume h: "rec_ci (Cn (Suc (Suc 0)) rec_valu [Cn (Suc (Suc 0)) rec_right [Cn (Suc (Suc 0)) 
    rec_conf [recf.id (Suc (Suc 0)) 0, recf.id (Suc (Suc 0)) (Suc 0), rec_halt]]]) =
    (F_ap, rs_pos, a_md)"
  moreover hence "rs_pos = Suc (Suc 0)"
    using cn_arity 
    by simp
  moreover obtain ap1 ar1 ft1 where a: "rec_ci 
    (Cn (Suc (Suc 0)) rec_right 
    [Cn (Suc (Suc 0)) rec_conf [recf.id (Suc (Suc 0)) 0, recf.id (Suc (Suc 0)) (Suc 0), rec_halt]]) = (ap1, ar1, ft1)"
    by(case_tac "rec_ci (Cn (Suc (Suc 0)) rec_right [Cn (Suc (Suc 0)) 
      rec_conf [recf.id (Suc (Suc 0)) 0, recf.id (Suc (Suc 0)) (Suc 0), rec_halt]])", auto)
  moreover hence b: "ar1 = Suc (Suc 0)"
    using cn_arity by simp
  ultimately show "?thesis"
  proof(rule_tac i = 0 in cn_unhalt_case, auto)
    fix anything
    obtain ap2 ar2 ft2 where c: 
      "rec_ci (Cn (Suc (Suc 0)) rec_conf [recf.id (Suc (Suc 0)) 0, recf.id (Suc (Suc 0)) (Suc 0), rec_halt])
      = (ap2, ar2, ft2)" 
      by(case_tac "rec_ci (Cn (Suc (Suc 0)) rec_conf
        [recf.id (Suc (Suc 0)) 0, recf.id (Suc (Suc 0)) (Suc 0), rec_halt])", auto)
    moreover hence d:"ar2 = Suc (Suc 0)"
      using cn_arity by simp
    ultimately have "{\<lambda>nl. nl = [code tp, bl2wc (<lm>)] @ 0 \<up> (ft1 - Suc (Suc 0)) @ anything} ap1 \<up>"
      using a b c d
    proof(rule_tac i = 0 in cn_unhalt_case, auto)
      fix anything
      obtain ap3 ar3 ft3 where e: "rec_ci rec_halt = (ap3, ar3, ft3)"
        by(case_tac "rec_ci rec_halt", auto)
      hence f: "ar3 = Suc (Suc 0)"
        using mn_arity
        by(simp add: rec_halt_def)
      have "{\<lambda>nl. nl = [code tp, bl2wc (<lm>)] @ 0 \<up> (ft2 - Suc (Suc 0)) @ anything} ap2 \<up>"
        using c d e f
      proof(rule_tac i = 2 in cn_unhalt_case, auto simp: rec_halt_def)
        fix anything
        have "{\<lambda>nl. nl = [code tp, bl2wc (<lm>)] @ 0 \<up> (ft3 - Suc (Suc 0)) @ anything} ap3 \<up>"
          using e f
        proof(rule_tac mn_unhalt_case, auto simp: rec_halt_def)
          fix i
          show "terminate rec_nonstop [code tp, bl2wc (<lm>), i]"
            by(rule_tac primerec_terminate, auto)
        next
          fix i
          show "0 < rec_exec rec_nonstop [code tp, bl2wc (<lm>), i]"
            using assms
            by(drule_tac nonstop_true, auto)
        qed
        thus "{\<lambda>nl. nl = code tp # bl2wc (<lm>) # 0 \<up> (ft3 - Suc (Suc 0)) @ anything} ap3 \<up>" by simp
      next
        fix apj arj ftj j  anything
        assume "j<2" "rec_ci ([recf.id (Suc (Suc 0)) 0, recf.id (Suc (Suc 0)) (Suc 0), Mn (Suc (Suc 0)) rec_nonstop] ! j) = (apj, arj, ftj)"
        hence "{\<lambda>nl. nl = [code tp, bl2wc (<lm>)] @ 0 \<up> (ftj - arj) @ anything} apj
          {\<lambda>nl. nl = [code tp, bl2wc (<lm>)] @
            rec_exec ([recf.id (Suc (Suc 0)) 0, recf.id (Suc (Suc 0)) (Suc 0), Mn (Suc (Suc 0)) rec_nonstop] ! j) [code tp, bl2wc (<lm>)] # 
               0 \<up> (ftj - Suc arj) @ anything}"
          apply(rule_tac recursive_compile_correct)
           apply(case_tac j, auto)
           apply(rule_tac [!] primerec_terminate)
          by(auto)
        thus "{\<lambda>nl. nl = code tp # bl2wc (<lm>) # 0 \<up> (ftj - arj) @ anything} apj
          {\<lambda>nl. nl = code tp # bl2wc (<lm>) # rec_exec ([recf.id (Suc (Suc 0)) 0, recf.id (Suc (Suc 0))
          (Suc 0), Mn (Suc (Suc 0)) rec_nonstop] ! j) [code tp, bl2wc (<lm>)] # 0 \<up> (ftj - Suc arj) @ anything}"
          by simp
      next
        fix j
        assume "(j::nat) < 2"
        thus "terminate ([recf.id (Suc (Suc 0)) 0, recf.id (Suc (Suc 0)) (Suc 0), Mn (Suc (Suc 0)) rec_nonstop] ! j)
          [code tp, bl2wc (<lm>)]"
          by(case_tac j, auto intro!: primerec_terminate)
      qed
      thus "{\<lambda>nl. nl = code tp # bl2wc (<lm>) # 0 \<up> (ft2 - Suc (Suc 0)) @ anything} ap2 \<up>"
        by simp
    qed
    thus "{\<lambda>nl. nl = code tp # bl2wc (<lm>) # 0 \<up> (ft1 - Suc (Suc 0)) @ anything} ap1 \<up>" by simp
  qed
qed

lemma uabc_uhalt': 
  "\<lbrakk>tm_wf (tp, 0);
  \<forall> stp. (\<not> TSTD (steps0 (Suc 0, Bk\<up>(l), <lm>) tp stp));
  rec_ci rec_F = (ap, pos, md)\<rbrakk>
  \<Longrightarrow> {\<lambda> nl. nl = [code tp, bl2wc (<lm>)]} ap \<up>"
proof(frule_tac F_ap = ap and rs_pos = pos and a_md = md
    and suflm = "[]" in F_aprog_uhalt, auto simp: abc_Hoare_unhalt_def, 
    case_tac "abc_steps_l (0, [code tp, bl2wc (<lm>)]) ap n", simp)
  fix n a b
  assume h: 
    "\<forall>n. abc_notfinal (abc_steps_l (0, code tp # bl2wc (<lm>) # 0 \<up> (md - pos)) ap n) ap"
    "abc_steps_l (0, [code tp, bl2wc (<lm>)]) ap n = (a, b)" 
    "tm_wf (tp, 0)" 
    "rec_ci rec_F = (ap, pos, md)"
  moreover have a: "ap \<noteq> []"
    using h rec_ci_not_null[of "rec_F" pos md] by auto
  ultimately show "a < length ap"
  proof(erule_tac x = n in allE)
    assume g: "abc_notfinal (abc_steps_l (0, code tp # bl2wc (<lm>) # 0 \<up> (md - pos)) ap n) ap"
    obtain ss nl where b : "abc_steps_l (0, code tp # bl2wc (<lm>) # 0 \<up> (md - pos)) ap n = (ss, nl)"
      by (metis prod.exhaust)
    then have c: "ss < length ap"
      using g by simp
    thus "?thesis"
      using a b c
      using abc_list_crsp_steps[of "[code tp, bl2wc (<lm>)]"
          "md - pos" ap n ss nl] h
      by(simp)
  qed
qed

lemma uabc_uhalt: 
  "\<lbrakk>tm_wf (tp, 0); 
  \<forall> stp. (\<not> TSTD (steps0 (Suc 0, Bk\<up>(l), <lm>) tp stp))\<rbrakk>
  \<Longrightarrow> {\<lambda> nl. nl = [code tp, bl2wc (<lm>)]} F_aprog \<up> "
proof -
  obtain a b c where abc:"rec_ci rec_F = (a,b,c)" by (cases "rec_ci rec_F") force
  assume a:"tm_wf (tp, 0)" "\<forall> stp. (\<not> TSTD (steps0 (Suc 0, Bk\<up>(l), <lm>) tp stp))"
  from uabc_uhalt'[OF a abc] abc_Hoare_plus_unhalt1
  show "{\<lambda> nl. nl = [code tp, bl2wc (<lm>)]} F_aprog \<up>"
    by(simp add: F_aprog_def abc)
qed

lemma tutm_uhalt': 
  assumes tm_wf:  "tm_wf (tp,0)"
    and unhalt: "\<forall> stp. (\<not> TSTD (steps0 (1, Bk\<up>(l), <lm>) tp stp))"
  shows "\<forall> stp. \<not> is_final (steps0 (1, [Bk, Bk], <[code tp, bl2wc (<lm>)]>) t_utm stp)"
  unfolding t_utm_def
proof(rule_tac compile_correct_unhalt, auto)
  show "F_tprog = tm_of F_aprog"
    by(simp add:  F_tprog_def)
next
  show "crsp (layout_of F_aprog) (0, [code tp, bl2wc (<lm>)]) (Suc 0, [Bk, Bk], <[code tp, bl2wc (<lm>)]>)  []"
    by(auto simp: crsp.simps start_of.simps)
next
  fix stp a b
  show "abc_steps_l (0, [code tp, bl2wc (<lm>)]) F_aprog stp = (a, b) \<Longrightarrow> a < length F_aprog"
    using assms
    apply(drule_tac uabc_uhalt, auto simp: abc_Hoare_unhalt_def)
    by(erule_tac x = stp in allE, erule_tac x = stp in allE, simp) 
qed

lemma tinres_commute: "tinres r r' \<Longrightarrow> tinres r' r"
  apply(auto simp: tinres_def)
  done

lemma inres_tape:
  "\<lbrakk>steps0 (st, l, r) tp stp = (a, b, c); steps0 (st, l', r') tp stp = (a', b', c'); 
  tinres l l'; tinres r r'\<rbrakk>
  \<Longrightarrow> a = a' \<and> tinres b b' \<and> tinres c c'"
proof(case_tac "steps0 (st, l', r) tp stp")
  fix aa ba ca
  assume h: "steps0 (st, l, r) tp stp = (a, b, c)" 
    "steps0 (st, l', r') tp stp = (a', b', c')"
    "tinres l l'" "tinres r r'"
    "steps0 (st, l', r) tp stp = (aa, ba, ca)"
  have "tinres b ba \<and> c = ca \<and> a = aa"
    using h
    apply(rule_tac tinres_steps1, auto)
    done
  moreover have "b' = ba \<and> tinres c' ca \<and> a' =  aa"
    using h
    apply(rule_tac tinres_steps2, auto intro: tinres_commute)
    done
  ultimately show "?thesis"
    apply(auto intro: tinres_commute)
    done
qed

lemma tape_normalize:
  assumes "\<forall> stp. \<not> is_final(steps0 (Suc 0, [Bk,Bk], <[code tp, bl2wc (<lm>)]>) t_utm stp)"
  shows   "\<forall> stp. \<not> is_final (steps0 (Suc 0, Bk\<up>(m), <[code tp, bl2wc (<lm>)]> @ Bk\<up>(n)) t_utm stp)"
    (is "\<forall> stp. ?P stp")
proof
  fix stp
  from assms[rule_format,of stp] show "?P stp"
    apply(case_tac "steps0 (Suc 0, Bk\<up>(m), <[code tp, bl2wc (<lm>)]> @ Bk\<up>(n)) t_utm stp", simp)
    apply(case_tac "steps0 (Suc 0, [Bk, Bk], <[code tp, bl2wc (<lm>)]>) t_utm stp", simp)
    apply(drule_tac inres_tape, auto)
     apply(auto simp: tinres_def)
    apply(case_tac "m > Suc (Suc 0)")
     apply(rule_tac x = "m - Suc (Suc 0)" in exI) 
     apply(case_tac m, simp_all)
     apply(metis Suc_lessD Suc_pred replicate_Suc)
    apply(rule_tac x = "2 - m" in exI, simp add: replicate_add[THEN sym])
    apply(simp only: numeral_2_eq_2, simp add: replicate_Suc)
    done
qed

lemma tutm_uhalt: 
  "\<lbrakk>tm_wf (tp,0);
    \<forall> stp. (\<not> TSTD (steps0 (Suc 0, Bk\<up>(l), <args>) tp stp))\<rbrakk>
  \<Longrightarrow> \<forall> stp. \<not> is_final (steps0 (Suc 0, Bk\<up>(m), <[code tp, bl2wc (<args>)]> @ Bk\<up>(n)) t_utm stp)"
  apply(rule_tac tape_normalize)
  apply(rule_tac tutm_uhalt'[simplified], simp_all)
  done

lemma UTM_uhalt_lemma_pre:
  assumes tm_wf: "tm_wf (tp, 0)"
    and exec: "\<forall> stp. (\<not> TSTD (steps0 (Suc 0, Bk\<up>(l), <args>) tp stp))"
    and args: "args \<noteq> []"
  shows "\<forall> stp. \<not> is_final (steps0 (Suc 0, [], <code tp # args>)  UTM_pre stp)"
proof -
  let ?P1 = "\<lambda> (l, r). l = [] \<and> r = <code tp # args>"
  let ?Q1 = "\<lambda> (l, r). (l = [Bk] \<and>
             (\<exists> rn. r = Oc\<up>(Suc (code tp)) @ Bk # Oc\<up>(Suc (bl_bin (<args>))) @ Bk\<up>(rn)))"
  let ?P2 = ?Q1
  have "{?P1} (t_wcode |+| t_utm) \<up>"
  proof(rule_tac Hoare_plus_unhalt)
    show "tm_wf (t_wcode, 0)" by auto
  next
    show "{?P1} t_wcode {?Q1}"
      apply(rule_tac Hoare_haltI, auto)
      using wcode_lemma_1[of args "code tp"] args
      apply(auto)
      by (metis (mono_tags, lifting) holds_for.simps is_finalI old.prod.case)
  next
    show "{?P2} t_utm \<up>"
    proof(rule_tac Hoare_unhaltI, auto)
      fix n rn
      assume h: "is_final (steps0 (Suc 0, [Bk], Oc \<up> Suc (code tp) @ Bk # Oc \<up> Suc (bl_bin (<args>)) @ Bk \<up> rn) t_utm n)"
      have "\<forall> stp. \<not> is_final (steps0 (Suc 0, Bk\<up>(Suc 0), <[code tp, bl2wc (<args>)]> @ Bk\<up>(rn)) t_utm stp)"
        using assms
        apply(rule_tac tutm_uhalt, simp_all)
        done
      thus "False"
        using h
        apply(erule_tac x = n in allE)
        apply(simp add: tape_of_list_def bin_wc_eq tape_of_nat_def)
        done
    qed
  qed
  thus "?thesis"
    apply(simp add: Hoare_unhalt_def UTM_pre_def)
    done
qed

text \<open>
  The correctness of \<open>UTM\<close>, the unhalt case.
\<close>

lemma UTM_uhalt_lemma':
  assumes tm_wf: "tm_wf (tp, 0)"
    and unhalt: "\<forall> stp. (\<not> TSTD (steps0 (Suc 0, Bk\<up>(l), <args>) tp stp))"
    and args: "args \<noteq> []"
  shows " \<forall> stp. \<not> is_final (steps0 (Suc 0, [], <code tp # args>)  UTM stp)"
  using UTM_uhalt_lemma_pre[of tp l args] assms
  apply(simp add: UTM_pre_def t_utm_def UTM_def F_aprog_def F_tprog_def)
  apply(case_tac "rec_ci rec_F", simp)
  done

lemma UTM_halt_lemma:
  assumes tm_wf: "tm_wf (p, 0)"
    and resut: "rs > 0"
    and args: "(args::nat list) \<noteq> []"
    and exec: "{(\<lambda>tp. tp = (Bk\<up>i, <args>))} p {(\<lambda>tp. tp = (Bk\<up>m, Oc\<up>rs @ Bk\<up>k))}" 
  shows "{(\<lambda>tp. tp = ([], <code p # args>))} UTM {(\<lambda>tp. (\<exists> m n. tp = (Bk\<up>m, Oc\<up>rs @ Bk\<up>n)))}"
proof -
  let ?steps0 = "steps0 (Suc 0, [], <code p # args>)"
  let ?stepsBk = "steps0 (Suc 0, Bk\<up>i, <args>) p"
  from wcode_lemma_1[OF args,of "code p"] obtain stp ln rn where
    wcl1:"?steps0 t_wcode stp =
     (0, [Bk], Oc \<up> Suc (code p) @ Bk # Oc \<up> Suc (bl_bin (<args>)) @ Bk \<up> rn)" by fast
  from exec Hoare_halt_def obtain n where
    n:"{\<lambda>tp. tp = (Bk \<up> i, <args>)} p {\<lambda>tp. tp = (Bk \<up> m, Oc \<up> rs @ Bk \<up> k)}"
    "is_final (?stepsBk n)"
    "(\<lambda>tp. tp = (Bk \<up> m, Oc \<up> rs @ Bk \<up> k)) holds_for steps0 (Suc 0, Bk \<up> i, <args>) p n"
    by auto
  obtain a where a:"a = fst (rec_ci rec_F)" by blast
  have "{(\<lambda> (l, r). l = [] \<and> r = <code p # args>)} (t_wcode |+| t_utm)
          {(\<lambda> (l, r). (\<exists> m. l = Bk\<up>m) \<and> (\<exists> n. r = Oc\<up>rs @ Bk\<up>n))}"
  proof(rule_tac Hoare_plus_halt)
    show "{\<lambda>(l, r). l = [] \<and> r = <code p # args>} t_wcode {\<lambda> (l, r). (l = [Bk] \<and>
    (\<exists> rn. r = Oc\<up>(Suc (code p)) @ Bk # Oc\<up>(Suc (bl_bin (<args>))) @ Bk\<up>(rn)))}"
      using wcl1 by (auto intro!:Hoare_haltI exI[of _ stp])
  next
    have "\<exists> stp. (?stepsBk stp = (0, Bk\<up>m, Oc\<up>rs @ Bk\<up>k))"
      using n by (case_tac "?stepsBk n", auto)
    then obtain stp where k: "steps0 (Suc 0, Bk\<up>i, <args>) p stp = (0, Bk\<up>m, Oc\<up>rs @ Bk\<up>k)"
      ..
    thus "{\<lambda>(l, r). l = [Bk] \<and> (\<exists>rn. r = Oc \<up> Suc (code p) @ Bk # Oc \<up> Suc (bl_bin (<args>)) @ Bk \<up> rn)}
      t_utm {\<lambda>(l, r). (\<exists>m. l = Bk \<up> m) \<and> (\<exists>n. r = Oc \<up> rs @ Bk \<up> n)}"
    proof(rule_tac Hoare_haltI, auto)
      fix rn
      from t_utm_halt_eq[OF assms(1) k assms(2),of rn] assms k
      have "\<exists> ma n stp. steps0 (Suc 0, [Bk], <[code p, bl2wc (<args>)]> @ Bk \<up> rn) t_utm stp =
       (0, Bk \<up> ma, Oc \<up> rs @ Bk \<up> n)" by (auto simp add: bin_wc_eq)
      then obtain stpx m' n' where
        t:"steps0 (Suc 0, [Bk], <[code p, bl2wc (<args>)]> @ Bk \<up> rn) t_utm stpx =
       (0, Bk \<up> m', Oc \<up> rs @ Bk \<up> n')" by auto
      show "\<exists>n. is_final (steps0 (Suc 0, [Bk], Oc \<up> Suc (code p) @ Bk # Oc \<up> Suc (bl_bin (<args>)) @ Bk \<up> rn) t_utm n) \<and>
             (\<lambda>(l, r). (\<exists>m. l = Bk \<up> m) \<and> (\<exists>n. r = Oc \<up> rs @ Bk \<up> n)) holds_for steps0 
         (Suc 0, [Bk], Oc \<up> Suc (code p) @ Bk # Oc \<up> Suc (bl_bin (<args>)) @ Bk \<up> rn) t_utm n"      
        using t
        by(auto simp: bin_wc_eq tape_of_list_def tape_of_nat_def intro:exI[of _ stpx])
    qed
  next
    show "tm_wf0 t_wcode" by auto
  qed
  then obtain n where
    "is_final (?steps0 (t_wcode |+| t_utm) n)" 
    "(\<lambda>(l, r). (\<exists>m. l = Bk \<up> m) \<and>
           (\<exists>n. r = Oc \<up> rs @ Bk \<up> n)) holds_for ?steps0 (t_wcode |+| t_utm) n"
    by(auto simp add: Hoare_halt_def a)
  thus "?thesis"
    apply(case_tac "rec_ci rec_F")
    apply(auto simp add: UTM_def Hoare_halt_def)
    apply(case_tac "(?steps0 (t_wcode |+| t_utm) n)")
    apply(rule_tac x="n" in exI)
    apply(auto simp add:a t_utm_def F_aprog_def F_tprog_def)
    done
qed

lemma UTM_halt_lemma2:
  assumes tm_wf: "tm_wf (p, 0)"
    and args: "(args::nat list) \<noteq> []"
    and exec: "{(\<lambda>tp. tp = ([], <args>))} p {(\<lambda>tp. tp = (Bk\<up>m, <(n::nat)> @ Bk\<up>k))}" 
  shows "{(\<lambda>tp. tp = ([], <code p # args>))} UTM {(\<lambda>tp. (\<exists> m k. tp = (Bk\<up>m, <n> @ Bk\<up>k)))}"
  using UTM_halt_lemma[OF assms(1) _ assms(2), where i="0"]
  using assms(3)
  by(simp add: tape_of_nat_def)

lemma UTM_unhalt_lemma: 
  assumes tm_wf: "tm_wf (p, 0)"
    and unhalt: "{(\<lambda>tp. tp = (Bk\<up>i, <args>))} p \<up>"
    and args: "args \<noteq> []"
  shows "{(\<lambda>tp. tp = ([], <code p # args>))} UTM \<up>"
proof -
  have "(\<not> TSTD (steps0 (Suc 0, Bk\<up>(i), <args>) p stp))" for stp
    (* in unhalt, we substitute inner 'forall' n\<rightarrow>stp *)
    using unhalt[unfolded Hoare_unhalt_def,rule_format,OF refl,of stp]
    by(cases "steps0 (Suc 0, Bk \<up> i, <args>) p stp",auto simp: Hoare_unhalt_def TSTD_def)
  then have "\<forall> stp. \<not> is_final (steps0 (Suc 0, [], <code p # args>)  UTM stp)"
    using assms by(intro UTM_uhalt_lemma', auto)
  thus "?thesis" by(simp add: Hoare_unhalt_def)
qed

lemma UTM_unhalt_lemma2: 
  assumes tm_wf: "tm_wf (p, 0)"
    and unhalt: "{(\<lambda>tp. tp = ([], <args>))} p \<up>"
    and args: "args \<noteq> []"
  shows "{(\<lambda>tp. tp = ([], <code p # args>))} UTM \<up>"
  using UTM_unhalt_lemma[OF assms(1), where i="0"]
  using assms(2-3)
  by(simp add: tape_of_nat_def)

end