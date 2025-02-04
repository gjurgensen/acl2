; Utilities dealing with invariant-risk
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also suppress-invariant-risk.lisp
;; See also books/std/system/invariant-risk.lisp.

(include-book "kestrel/utilities/world" :dir :system) ; todo: reduce, for all-functions-in-world

;; Keeps the elements of FNS that have invariant-risk.
(defun filter-invariant-risk-functions (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (if (endp fns)
      nil
    (let* ((fn (first fns))
           (invariant-riskp (getpropc fn 'invariant-risk nil wrld)))
      (if invariant-riskp
          (cons fn (filter-invariant-risk-functions (rest fns) wrld))
        (filter-invariant-risk-functions (rest fns) wrld)))))

(defthm symbol-listp-of-filter-invariant-risk-functions
  (implies (and (plist-worldp wrld)
                (symbol-listp fns))
           (symbol-listp (filter-invariant-risk-functions fns wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Keeps the elements of FNS (a list of functions in WRLD) that are in :program
;; mode.
(defun filter-program-mode-functions (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (if (endp fns)
      nil
    (let ((fn (first fns)))
      (if (programp fn wrld)
          (cons fn (filter-program-mode-functions (rest fns) wrld))
        (filter-program-mode-functions (rest fns) wrld)))))

(defthm symbol-listp-of-filter-program-mode-functions
  (implies (and (plist-worldp wrld)
                (symbol-listp fns))
           (symbol-listp (filter-program-mode-functions fns wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv logic-functions program-functions).
(defun classify-functions (fns wrld logic-acc program-acc)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (if (endp fns)
      (mv logic-acc program-acc)
    (let ((fn (first fns)))
      (if (programp fn wrld)
          (classify-functions (rest fns) wrld logic-acc (cons fn program-acc))
        (classify-functions (rest fns) wrld (cons fn logic-acc) program-acc)))))

(defthm symbol-listp-of-mv-nth-0-of-classify-functions
  (implies (and ;(plist-worldp wrld)
                (symbol-listp fns)
                (symbol-listp logic-acc))
           (symbol-listp (mv-nth 0 (classify-functions fns wrld logic-acc program-acc)))))

(defthm symbol-listp-of-mv-nth-1-of-classify-functions
  (implies (and ;(plist-worldp wrld)
                (symbol-listp fns)
                (symbol-listp program-acc))
           (symbol-listp (mv-nth 1 (classify-functions fns wrld logic-acc program-acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of all functions in WRLD that have invariant-risk
(defund invariant-risk-functions-in-world (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let* ((all-functions (all-functions-in-world wrld)))
    (filter-invariant-risk-functions all-functions wrld)))

(defthm symbol-listp-of-invariant-risk-functions-in-world
  (implies (plist-worldp wrld)
           (symbol-listp (invariant-risk-functions-in-world wrld)))
  :hints (("Goal" :in-theory (enable invariant-risk-functions-in-world))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the list of all :program mode functions with invariant-risk in the
;; current world.  Example use: (invariant-risk-program-mode-functions-in-world (w state))
(defun invariant-risk-program-mode-functions-in-world (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (filter-program-mode-functions (invariant-risk-functions-in-world wrld) wrld))

(defthm symbol-listp-of-invariant-risk-program-mode-functions-in-world
  (implies (plist-worldp wrld)
           (symbol-listp (invariant-risk-program-mode-functions-in-world wrld)))
  :hints (("Goal" :in-theory (enable invariant-risk-program-mode-functions-in-world))))

;; OLD:
;; (let (ans)
;;   (dolist (p (list-all-packages))
;;     (do-symbols (sym p)
;;       (when (and (getpropc sym 'invariant-risk)
;;                  (eq :program (getpropc sym 'symbol-class)) ;; remove this to also see logic mode functions
;;                  (not (getpropc sym 'predefined)))
;;         (push sym ans))))
;;   ans)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun invariant-risk-report-fn (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (let ((fns (invariant-risk-functions-in-world wrld)))
    (mv-let (logic-functions program-functions)
      (classify-functions fns wrld nil nil)
      (progn$ (cw ":logic functions with invariant-risk: ~X01.~%" logic-functions nil)
              (cw ":program functions with invariant-risk: ~X01.~%" program-functions nil)))))

(defmacro invariant-risk-report ()
  '(invariant-risk-report-fn (w state)))
