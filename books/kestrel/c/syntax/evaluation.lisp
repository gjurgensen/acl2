; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-operations")
(include-book "types")

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/strings/hex" :dir :system) ;; For dec/oct/hex-const->value

(include-book "kestrel/utilities/arith-fix-and-equiv-defs" :dir :system)

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

(local (include-book "kestrel/utilities/arith-fix-and-equiv" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Evaluation of constant expressions is needed to fully validate C programs.
;; Here, we provide partial support for evaluation.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes values/value-list
  :short "Fixtypes of values and value lists."

  ;; Note: this is creating definitions in ACL2 package because 'value is in
  ;; the ACL2 package.
  (fty::deftagsum value
    :short "Fixtype of values."
    (:unknown ())
    (:bool   ((get nat)))
    (:uchar  ((get nat)))
    (:schar  ((get int)))
    (:ushort ((get nat)))
    (:sshort ((get int)))
    (:uint   ((get nat)))
    (:sint   ((get int)))
    (:ulong  ((get nat)))
    (:slong  ((get int)))
    (:ullong ((get nat)))
    (:sllong ((get int)))
    (:array  ((elements value-list)))
    :pred valuep
    :prepwork ((local (in-theory (enable nfix ifix)))))

  (fty::deflist value-list
    :short "Fixtype of lists of values."
    :elt-type value
    :true-listp t
    :elementp-of-nil nil
    :pred value-listp))

;;;;;;;;;;;;;;;;;;;;

;; Validity under a particular ienv
(defines well-formed-value/value-list-p
  (define well-formed-value-p ((value valuep) (ienv ienvp))
    :returns (yes/no booleanp)
    (b* (((ienv ienv) ienv))
      (acl2::value-case
        value
        :unknown t
        :bool (unsigned-byte-p value.get ienv.bool-bytes)
        :uchar (unsigned-byte-p value.get 1)
        :schar (signed-byte-p value.get 1)
        :ushort (unsigned-byte-p value.get ienv.short-bytes)
        :sshort (signed-byte-p value.get ienv.short-bytes)
        :uint (unsigned-byte-p value.get ienv.int-bytes)
        :sint (signed-byte-p value.get ienv.int-bytes)
        :ulong (unsigned-byte-p value.get ienv.long-bytes)
        :slong (signed-byte-p value.get ienv.long-bytes)
        :ullong (unsigned-byte-p value.get ienv.llong-bytes)
        :sllong (signed-byte-p value.get ienv.llong-bytes)
        :array (well-formed-value-list-p value.elements ienv)))
    :measure (acl2::value-count value))

  (define well-formed-value-list-p ((values value-listp) (ienv ienvp))
    :returns (yes/no booleanp)
    (or (endp values)
        (and (well-formed-value-p (first values) ienv)
             (well-formed-value-list-p (rest values) ienv)))
    :measure (value-list-count values)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define integer-from-value ((value valuep))
  :returns (integer? acl2::maybe-integerp)
  (acl2::value-case
   value
   :unknown nil
   :bool value.get
   :uchar value.get
   :schar value.get
   :ushort value.get
   :sshort value.get
   :uint value.get
   :sint value.get
   :ulong value.get
   :slong value.get
   :ullong value.get
   :sllong value.get
   :array nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; MOVE to abstract-syntax-operations
(define dec/oct/hex-const->value ((const dec/oct/hex-constp))
  :returns (value natp)
  (dec/oct/hex-const-case
    const
    :dec const.value
    :oct const.value
    :hex (str::hex-digit-chars-value const.digits)))

;;;;;;;;;;;;;;;;;;;;

;; [C17:6.4.4.1/5]
(define eval-iconst ((iconst iconstp) (ienv ienvp))
  :returns (val valuep)
  (b* (((iconst iconst) iconst)
       ((ienv ienv) ienv)
       (num (dec/oct/hex-const->value iconst.core)))
    (isuffix-option-case
      iconst.suffix?
      :some (isuffix-case
              iconst.suffix?.val
              :u (cond ((unsigned-byte-p num ienv.int-bytes)
                        (acl2::value-uint num))
                       ((unsigned-byte-p num ienv.long-bytes)
                        (acl2::value-ulong num))
                       ((unsigned-byte-p num ienv.llong-bytes)
                        (acl2::value-ullong num))
                       (t
                        ;; We could consider returning an error here
                        (acl2::value-unknown)))
              :l (if (lsuffix-case iconst.suffix?.val.length
                                   '(:locase-l :upcase-l))
                     (cond ((signed-byte-p num ienv.long-bytes)
                            (acl2::value-slong num))
                           ((signed-byte-p num ienv.llong-bytes)
                            (acl2::value-sllong num))
                           (t (acl2::value-unknown)))
                   ;; lsuffix-kind is :locase-ll or :upcase-ll
                   (cond ((signed-byte-p num ienv.llong-bytes)
                          (acl2::value-sllong num))
                         (t (acl2::value-unknown))))
              :ul (if (lsuffix-case iconst.suffix?.val.length
                                   '(:locase-l :upcase-l))
                     (cond ((unsigned-byte-p num ienv.long-bytes)
                            (acl2::value-ulong num))
                           ((unsigned-byte-p num ienv.llong-bytes)
                            (acl2::value-ullong num))
                           (t (acl2::value-unknown)))
                   ;; lsuffix-kind is :locase-ll or :upcase-ll
                   (cond ((unsigned-byte-p num ienv.llong-bytes)
                          (acl2::value-ullong num))
                         (t (acl2::value-unknown))))
              :lu (if (lsuffix-case iconst.suffix?.val.length
                                    '(:locase-l :upcase-l))
                      (cond ((unsigned-byte-p num ienv.long-bytes)
                             (acl2::value-ulong num))
                            ((unsigned-byte-p num ienv.llong-bytes)
                             (acl2::value-ullong num))
                            (t (acl2::value-unknown)))
                    ;; lsuffix-kind is :locase-ll or :upcase-ll
                    (cond ((unsigned-byte-p num ienv.llong-bytes)
                           (acl2::value-ullong num))
                          (t (acl2::value-unknown)))))
      :none (dec/oct/hex-const-case
              iconst.core
              :dec (cond ((signed-byte-p num ienv.int-bytes)
                          (acl2::value-sint num))
                         ((signed-byte-p num ienv.long-bytes)
                          (acl2::value-slong num))
                         ((signed-byte-p num ienv.llong-bytes)
                          (acl2::value-sllong num))
                         (t (acl2::value-unknown)))
              :otherwise (cond ((signed-byte-p num ienv.int-bytes)
                                (acl2::value-sint num))
                               ((unsigned-byte-p num ienv.int-bytes)
                                (acl2::value-uint num))
                               ((signed-byte-p num ienv.long-bytes)
                                (acl2::value-slong num))
                               ((unsigned-byte-p num ienv.long-bytes)
                                (acl2::value-ulong num))
                               ((signed-byte-p num ienv.llong-bytes)
                                (acl2::value-sllong num))
                               ((unsigned-byte-p num ienv.llong-bytes)
                                (acl2::value-ullong num))
                               (t (acl2::value-unknown)))))))

(defrule well-formed-value-p-of-eval-iconst
  (well-formed-value-p (eval-iconst iconst ienv) ienv)
  :enable (eval-iconst
           well-formed-value-p
           ifix
           nfix))

;;;;;;;;;;;;;;;;;;;;

(define eval-const ((const constp) (ienv ienvp))
  :returns (val valuep)
  (const-case
    const
    :int (eval-iconst const.iconst ienv)
    :float (acl2::value-unknown)
    :enum (acl2::value-unknown)
    :char (acl2::value-unknown)))

(defrule well-formed-value-p-of-eval-const
  (well-formed-value-p (eval-const const ienv) ienv)
  :enable (eval-const
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;

(define eval-expr ((expr exprp) (ienv ienvp))
  :returns (val valuep)
  (expr-case
    expr
    :const (eval-const expr.const ienv)
    :paren (eval-expr expr.inner ienv)
    :otherwise (acl2::value-unknown))
  :measure (expr-count expr))

(defrule well-formed-value-p-of-eval-expr
  (well-formed-value-p (eval-expr expr ienv) ienv)
  :induct t
  :enable (eval-expr
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;

(define eval-const-expr ((expr const-exprp) (ienv ienvp))
  :returns (val valuep)
  (eval-expr (const-expr->expr expr) ienv))

(defrule well-formed-value-p-of-eval-const-expr
  (well-formed-value-p (eval-const-expr expr ienv) ienv)
  :enable (eval-const-expr
           well-formed-value-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-integer-constant-expr ((expr const-exprp) (ienv ienvp))
  :returns (integer? acl2::maybe-integerp)
  (integer-from-value (eval-const-expr expr ienv)))
