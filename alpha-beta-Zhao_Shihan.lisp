;; ====================================
;;  CMPU-365, Spring 2019
;;  Asmt. 4
;;  alpha-beta-template.lisp
;;  Feb. 28, 2019
;;  ZHAO SHIHAN
;; ====================================

;;  COMPUTE-MOVE
;; -------------------------------------------------------------
;;  INPUTS:  G, a CHESS struct
;;           CUTOFF-DEPTH, to limit depth of minimax search
;;  OUTPUT:  The best move according to MINIMAX with ALPHA-BETA
;;   pruning, using the static eval func, EVAL-FUNC.  Searches to
;;   a depth of CUTOFF-DEPTH.

(defun compute-move (g cutoff-depth)
  (let*
    ((statty (make-stats))
     (best-move
      (compute-max g 0 *neg-inf* *pos-inf* statty cutoff-depth))
     (num-moves-done (stats-num-moves-done statty))
     (num-potential-moves (stats-num-potential-moves statty))
     (num-moves-pruned (- num-potential-moves num-moves-done)))
    (format t "~%   ROOT NODE ALPHA: ~d~%" (eval-func g))
    (format t "   NUM-MOVES-DONE: ~d, NUM-MOVES-PRUNED: ~d~%"
            num-moves-done
            num-moves-pruned)
    (format t "   BEST MOVE: (~d ~d ~d ~d)~%"
            (first best-move)
            (second best-move)
            (third best-move)
            (fourth best-move))
    best-move))


;;  COMPUTE-MAX / COMPUTE-MIN
;; ---------------------------------------------------------------
;;  INPUTS:  G, a CHESS struct
;;           CURR-DEPTH, the current depth in the search
;;           ALPHA, BETA, alpha/beta values for this node in search
;;           STATTY, stats struct
;;           CUTOFF-DEPTH, to limit depth of minimax search
;;  OUTPUT:  If CURR-DEPTH is zero, returns best move
;;           Otherwise returns value of this node according
;;           to MINIMAX with ALPHA-BETA pruning.

;; This function and compute-min both generally mirror the pseudocodes
;; shown below:
;; ---------------------------------------------------------------

;;function compute-max (g, curr-depth, alpha, beta, statty, cutoff-depth)
;;    if (curr-depth == cutoff-depth)
;;      return static eval
;;    else if (game over)
;;      return win/loss score
;;    else
;;       current-max = -infinity
;;		   for each child of g
;;			    child-backprop = compute-max(child, depth + 1, [same as parent])
;;			 current-max = max(current-max, child-backprop)
;;			 alpha = max(alpha, child-backprop)
;;			 if beta <= alpha
;;				  break
;;		return current-max

;; ---------------------------------------------------------------

(defun compute-max (g curr-depth alpha beta statty cutoff-depth)
  (let
    ;; PATHS is an array containing all the legal moves from struct g
    ((paths (legal-moves g))
     ;; CURRENT-MAX is a number used to get the maximum eval score
     ;; among the children of g
     (current-max *neg-inf*)
     ;; CURRENT-MAX-IND is a number used to get the best move at the
     ;; root; it is an index of the move within PATHS array that
     ;; gives the maximum eval value
     ;; initialized to be -1 so that we know if it isn't modified
     ;; e.g. when cutoff-depth is 0, in which case just return
     ;; NIL
     (current-max-ind -1)
     ;; For each search node, we need its alpha value to be variable
     ;; because we will pass its updated value to its children.
     ;; A pointer would conveniently accomplish this requirement, but
     ;; parameters are passed by value in Lisp.
     ;; Therefore for each search node, we set aside a local pointer to
     ;; be updated. The pointer will take its starting value from the
     ;; alpha passed in as parameter, but can be frequently updated
     ;; each child will be given the alpha value of its direct parent's
     ;; local pointer at the time of calling.
     ;; compute-min uses the same strategy but with beta.
     (alf alpha))
    ;; update num-potential-moves by the length of PATHS
    ;; i.e. num of moves added to the search space
    (setf (stats-num-potential-moves statty)
          (+ (stats-num-potential-moves statty)
             (length paths)))
    (cond
      ;; Case 1: reached depth limit, return static eval
      ((= curr-depth cutoff-depth)
       (eval-func g))
      ;; Case 2: game over
      ((game-over? g)
       ;; white always runs compute-max
       ;; so if the game is over and white's king is still alive,
       ;; white (i.e. the side running compute-max) must be the
       ;; winning side, otherwise black must be the winning side
       (if (piece-live? (aref (chess-pieces g) *white* *king-index*))
         (- *win-value* curr-depth)
         (+ *loss-value* curr-depth)))
      ;; Case 3: else
      (t
       ;; for all moves in paths array, each move corresponding to a child
       (mapcar
        #'(lambda
           (path)
           (let
             ;; calculate the child's eval
             ;; call compute-min, since the next level has to be
             ;; a min node
             ;; apply one of the legal moves to get the child board
             ;; use curr-depth++
             ;; use the value of aforementioned alpha local pointer alf
             ;; the remaining parameters are simply passed down the tree
             ((child-backprop
               ;; this call modifies g
               ;; therefore must immediately undo after getting eval
               (compute-min (apply #'do-move! g nil path)
                            (+ curr-depth 1)
                            alf
                            beta
                            statty
                            cutoff-depth))
              ;; correspond to current-max-id
              ;; used to keep track of the current index into PATHS
              (curr-ind 0))
             (progn
              ;; we just explored a branch
              ;; increment number of moves done by 1 in STATS
              (incf (stats-num-moves-done statty))
              ;; undo
              (undo-move! g)
              ;; current-max = max(current-max, child-backprop)
              (when
                (> child-backprop current-max)
                (when
                  ;; only keep track of the best move when
                  ;; at root node
                  (= curr-depth 0)
                  (setf current-max-ind curr-ind))
                ;; otherwise just update max eval value
                (setf current-max child-backprop))
              ;; alpha = max(alpha, child-backprop)
              (when
                (> child-backprop alf)
                (setf alf child-backprop))
              ;; if beta <= alpha
              ;;		break
              (when
                (<= beta current-max)
                ;; when breaking at root node, we want to return
                ;; the best move rather than the maximum eval
                (if (= curr-depth 0)
                  ;; if conditions don't allow for the exploration
                  ;; return nil
                  (if (not (= current-max-ind -1))
                    (return-from compute-max (nth current-max-ind paths))
                    (return-from compute-max nil))
                  (return-from compute-max current-max)))
              ;; when at root node, update current index for every
              ;; iteration
              (when
                (= curr-depth 0)
                (incf curr-ind)))))
        paths)
        ;; if there is no pruning possible, just return
        ;; best eval/best move
        (if (= curr-depth 0)
          (if (not (= current-max-ind -1))
            (nth current-max-ind paths)
            nil)
          current-max)))))

;;  COMPUTE-MIN
;; -------------------------------------------------------
;;  INPUTS:  G, a CHESS struct
;;           CURR-DEPTH, the depth of this MIN node
;;           ALPHA, BETA, values received from parent MAX node
;;           STATTY, a stats struct
;;           CUTOFF-DEPTH, to limit depth of minimax search
;;  OUTPUT:  The value of this MIN node according to rules
;;           of MINIMAX with ALPHA-BETA pruning

;; because of the similarity of this function to compute-max, I will
;; just highlight a few changes
(defun compute-min (g curr-depth alpha beta statty cutoff-depth)
  (let
    ;; No need to write codes for the tree root condition
    ;; because compute-min is typically never run first.
    ((paths (legal-moves g))
     (current-min *pos-inf*)
     (bet beta))
    (setf (stats-num-potential-moves statty)
          (+ (stats-num-potential-moves statty)
             (length paths)))
    (cond
      ((= curr-depth cutoff-depth)
       (eval-func g))
      ((game-over? g)
       ;; black always runs compute-min
       ;; so if the game is over and black's king is still alive,
       ;; black (i.e. the side running compute-max) must be the
       ;; winning side, otherwise white must be the winning side
       (if (piece-live? (aref (chess-pieces g) *black* *king-index*))
         (- *win-value* curr-depth)
         (+ *loss-value* curr-depth)))
      (t
       (mapcar
        #'(lambda
           (path)
           (let
             ((child-backprop
               (compute-max (apply #'do-move! g nil path)
                            (+ curr-depth 1)
                            alpha
                            bet
                            statty
                            cutoff-depth)))
             (progn
              (incf (stats-num-moves-done statty))
              (undo-move! g)
              ;; current-min = min(child-backprop, current-min)
              (when
                (< child-backprop current-min)
                (setf current-min child-backprop))
              ;; beta = min(child-backprop, beta)
              (when
                (< child-backprop bet)
                (setf bet child-backprop))
              (when
                (<= current-min alpha)
                ;; return current-min instead of current max
                (return-from compute-min current-min)))))
        paths)
       current-min))))


;;  MY-TEST
;; -------------------------------
;; taken from: https://www.kidchess.com/play-chess/checkmate-the-king/
;; This simple scenario has 2 white rooks and 1 white king
;; facing off against 1 black king;
;; White should be able to checkmate black's king within 3 steps
;; therefore white should win in 4 steps

(defun my-test ()
  (problem "2R + K vs. K")
  (let ((g (init-game (list (list *king* 0 1)
                            (list *rook* 0 4)
                            (list *rook* 2 5))
                      (list (list *king* 3 3)))))
    (compute-do-and-show-n-moves g 4 4)
    (format t "White should have taken black's king by now!~%")
    (format t "Game over? ~A~%" (game-over? g)))
  )
