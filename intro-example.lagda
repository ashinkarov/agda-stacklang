\begin{code}[hide]
open import Data.Nat as ℕ using (ℕ; zero; suc; _+_; _*_) renaming (_∸_ to _-_; _≤ᵇ_ to _≤_; _<ᵇ_ to _<_)
open import psembedding hiding (sqsum)
\end{code}

\begin{figure}
\begin{subfigure}[b]{\columnwidth}
\centering
\begin{code}
sqsum : Stack (2 + n) → Stack (1 + n)
sqsum s = s ▹ dup ▹ mul ▹ exch ▹ dup ▹ mul ▹ exch ▹ add
\end{code}
\end{subfigure}
\begin{subfigure}[b]{\columnwidth}
\centering
\begin{minipage}{.7\columnwidth}
\begin{lstlisting}[language=PostScript]
/sqsum {
  dup mul exch dup mul exch add
} def
\end{lstlisting}
\end{minipage}
\end{subfigure}
\caption{A function definition for computing the sum of squares $a^2 +
b^2$ of the two topmost stack elements, written in our embedding of
PostScript in Agda (top) and the code produced by our reflection-based
extractor (bottom). The Agda type ensures that the input stack has at
least two elements, and that the output stack has one fewer element
than the input stack. The embedding is explained in full in
\secref{embedding} and the extractor in \secref{extraction}.}
\label{fig:sqsum}
\end{figure}
