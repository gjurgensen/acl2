; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)

(include-book "kestrel/utilities/messages" :dir :system)

(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/code-ensembles")
(include-book "../syntax/unambiguity")
(include-book "../syntax/validation-information")
(include-book "utilities/collect-idents")
(include-book "utilities/fresh-ident")

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap uid-ident-map
  :key-type c$::uid
  :val-type ident
  :pred uid-ident-mapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define split-struct-declors
  ((right-set ident-setp)
   (struct-declors struct-declor-listp))
  :returns (mv (struct-declors-left struct-declor-listp)
               (struct-declors-right struct-declor-listp))
  (b* ((right-set (ident-set-fix right-set))
       ((when (endp struct-declors))
        (mv nil nil))
       ((mv struct-declors-left struct-declors-right)
        (split-struct-declors right-set (rest struct-declors)))
       (struct-declor (struct-declor-fix (first struct-declors)))
       (declor? (c$::struct-declor->declor? struct-declor)))
    (if (and declor?
             (in (declor->ident declor?) right-set))
        (mv struct-declors-left (cons struct-declor struct-declors-right))
      (mv (cons struct-declor struct-declors-left) struct-declors-right))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines exprs/decls/stmts-peel
  (define expr-peel
    ((expr exprp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (expr-unambp expr)
                (expr-annop expr))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (expr1 exprp)
                 (expr2 exprp)
                 (objs$ uid-ident-mapp))
    (b* ((expr (expr-fix expr))
         (objs (uid-ident-map-fix objs))
         ((reterr) nil expr (irr-expr) objs))
      (expr-case
        expr
        :ident
        (b* (((var-info info) expr.info)
             (ident? (omap::assoc info.uid objs))
             ((unless ident?)
              (retok nil expr (irr-expr) objs))
             (expr-right (make-expr-ident :ident ident? :info nil)))
          (retok t expr expr-right objs))
        :const
        (retok nil expr (irr-expr) objs)
        :string
        (retok nil expr (irr-expr) objs)
        :paren
        (b* (((erp splitp expr1 expr2 objs)
              (expr-peel expr.inner struct-uid right-name right-set objs)))
          (retok splitp
                 (expr-paren expr1)
                 (if splitp (expr-paren expr2) (irr-expr))
                 objs))
        :gensel
        (b* (((erp control-splitp control - objs)
              (expr-peel expr.control struct-uid right-name right-set objs))
             ((erp assocs objs)
              (genassoc-list-peel
                expr.assocs struct-uid right-name right-set objs))
             ((when control-splitp)
              ;; TODO: think about whether this can be supported.
              (retmsg$ "Splits are not supported in ~
                        generic selection expressions.")))
          (retok nil
                 (make-expr-gensel :control control :assocs assocs)
                 (irr-expr)
                 objs))
        :arrsub
        (b* (((erp arg1-splitp arg1 - objs)
              (expr-peel expr.arg1 struct-uid right-name right-set objs))
             ((when arg1-splitp)
              ;; TODO: support this once array types derived from the
              ;;   target struct type is supported.
              (retmsg$ "Splits are not supported in ~
                        array subscripting expressions."))
             ((erp arg2-slitp arg2 - objs)
              (expr-peel expr.arg2 struct-uid right-name right-set objs))
             ((when arg2-splitp)
              (retmsg$ "Splits are not supported in array subscripts.")))
          (retok nil
                 (change-expr-arrsub expr :arg1 arg1 :arg2 arg2)
                 (irr-expr)
                 objs))
        :funcall
        (b* (((erp fun-splitp fun - objs)
              (expr-peel expr.fun struct-uid right-name right-set objs))
             ((when fun2?)
              (retmsg$ "Splits are not supported in function expressions."))
             ((erp args-splitp args - objs)
              (expr-list-peel expr.args struct-uid right-name right-set objs))
             ((when args-splitp)
              (retmsg$ "Splits are not supported in ~
                        function call argument lists.")))
          (retok nil
                 (change-expr-funcall expr :fun fun :args args)
                 (irr-expr)
                 objs))
        :member
        (b* ((arg-type (expr-type expr.arg)))
          (type-case
            arg-type
            :struct
            (b* (((erp arg-splitp arg1 arg2 objs)
                  (expr-peel expr.arg struct-uid right-name right-set objs))
                 ((unless arg-splitp)
                  (retok nil
                         (make-expr-member :arg arg1 :name expr.name)
                         (irr-expr)
                         objs))
                 ((unless (c$::uid-equal arg-type.uid struct-uid))
                  (retmsg$ "Splits are not supported in ~
                            member access expression lvalues.")))
              (retok nil
                     (make-expr-member :arg (if (in expr.name right-set)
                                                arg2
                                              arg1)
                                       :name expr.name)
                     (irr-expr)
                     objs))
            :unknown
            ;; TODO: If we had the full set of struct names handy,
            ;;   we could determine that many such cases are safe
            ;;   (when the name is not a member of the set).
            (retmsg$ "Cannot transform member access expression ~
                      with lvalue of unknown type.")
            :otherwise ;; :union, if well-typed.
            (b* (((erp arg-splitp arg - objs)
                  (expr-peel expr.arg struct-uid right-name right-set objs))
                 ((when arg-splitp)
                  (retmsg$ "Splits are not supported in ~
                            member access expression lvalues.")))
              (retok nil
                     (make-expr-member :arg arg :name expr.name)
                     (irr-expr)
                     objs))))
        :memberp
        (b* ((arg-type (expr-type expr.arg))
             ((erp arg-pointer-type)
              (b* (((reterr) nil))
                (type-case
                  arg-type
                  :pointer (retok arg-type.to)
                  :unknown ;; TODO: same as other unknown cases.
                  (retmsg$ "Cannot transform member access expression ~
                            with lvalue of unknown type.")
                  :otherwise
                  (retmsg$ "Ill-typed indirect member access expression.")))))
          (type-case
            arg-pointer-type
            :struct
            (b* (((erp arg-splitp arg1 arg2 objs)
                  (expr-peel expr.arg struct-uid right-name right-set objs))
                 ((unless arg-splitp)
                  (retok nil
                         (make-expr-member :arg arg1 :name expr.name)
                         (irr-expr)
                         objs))
                 ((unless (c$::uid-equal arg-type.uid struct-uid))
                  (retmsg$ "Splits are not supported in ~
                            member access expression lvalues.")))
              (retok nil
                     (make-expr-member :arg (if (in expr.name right-set)
                                                arg2
                                              arg1)
                                       :name expr.name)
                     (irr-expr)
                     objs))
            :unknown
            ;; TODO: If we had the full set of struct names handy,
            ;;   we could determine that many such cases are safe
            ;;   (when the name is not a member of the set).
            (retmsg$ "Cannot transform member access expression ~
                      with lvalue of unknown type.")
            :otherwise ;; :union, if well-typed.
            (b* (((erp arg-splitp arg - objs)
                  (expr-peel expr.arg struct-uid right-name right-set objs))
                 ((when arg-splitp)
                  (retmsg$ "Splits are not supported in ~
                            member access expression lvalues.")))
              (retok nil
                     (make-expr-member :arg arg :name expr.name)
                     (irr-expr)
                     objs))))
        :complit ;; TODO: support
        (retmsg$ "Compound literals are not yet supported.")
        :unary
        (b* (((erp arg-splitp arg1 arg2 objs)
              (expr-peel expr.arg struct-uid right-name right-set objs))
             ((unless arg-splitp)
              (retok nil
                     (make-expr-unop :unop expr.unop :arg arg1 :info nil)
                     (irr-expr)
                     objs))
             ;; We disallow impure operators.
             ((when (member-eq (unop-kind expr.unop)
                               '(:preinc :predec :postinc :postdec)))
              (retmsg$ "Splits are not supported for unary operator ~x0."
                       (unop-kind expr.unop))))
          (retok t
                 (make-expr-unary :unop expr.unop :arg arg1 :info nil)
                 (make-expr-unary :unop expr.unop :arg arg2 :info nil)
                 objs))
        :label-addr
        (b* (((erp arg-splitp arg - objs)
              (expr-peel expr.arg struct-uid right-name right-set objs))
             ((when arg-splitp)
              (retmsg$ "Splits are not supported in ~
                        label address expressions.")))
          (retok nil
                 (expr-label-addr arg)
                 (irr-expr)
                 objs))
        :sizeof
        (b* (((erp tyname-splitp tyname1 tyname2 objs)
              (tyname-peel expr.type struct-uid right-name right-set objs)))
          (retok tyname-splitp
                 (expr-sizeof tyname1)
                 (if tyname-splitp (expr-sizeof tyname1) (irr-expr))
                 objs))

        :alignof
        (b* (((erp tyname-splitp tyname1 tyname2 objs)
              (tyname-peel expr.type struct-uid right-name right-set objs)))
          (retok tyname-splitp
                 (change-expr-alignof expr :type tyname1)
                 (if tyname-splitp
                     (change-expr-alignof expr :type tyname2)
                   (irr-expr))
                 objs))
        ;; TODO: definitely have a test case for casts
        ;; Such as `x = (struct foo *)y`.
        :cast
        (expr-cast (tyname-peel (c$::expr-cast->type expr) objs)
        ;; Only allow for simple assignment (binop :asg)
        :binary
        (b* (((erp arg1-splitp arg1$1 arg1$2 objs)
              (expr-peel expr.arg1 struct-uid right-name right-set objs))
             ((erp arg1-splitp arg2$1 arg2$2 objs)
              (expr-peel expr.arg2 struct-uid right-name right-set objs))
             ((unless (or arg1-splitp arg2-splitp))
              (retok nil
                     (make-expr-binary :op expr.binop
                                       :arg1 arg1$1
                                       :arg2 arg2$1
                                       :info nil)
                     (irr-expr)
                     objs))
             ((unless (and arg1-splitp arg2-splitp))
              ;; This might occur if an integer is added to a struct pointer.
              ;; For now we disallow it.
              (retmsg$ "Binary operator expression can only be split if ~
                        both arguments are split."))
             ;; Outside of simple assignment, we could also see struct pointers
             ;; involved in comparison expressions.
             ;; For now, we disallow them.
             ((unless (binop-case expr.op :asg))
              (retmsg$ "Splits are not supported for ~
                        binary operator expressions ~
                        other than simple assignment.")))
          (retok t
                 (make-expr-binary :op expr.binop
                                   :arg1 arg1$1
                                   :arg2 arg2$1
                                   :info nil)
                 (make-expr-binary :op expr.binop
                                   :arg1 arg1$2
                                   :arg2 arg2$2
                                   :info nil)
                 objs))
        ;; TODO: definitely test
        :cond
        (b* (((erp test-splitp test - objs)
              (expr-peel expr.test struct-uid right-name right-set objs))
             ((when test-slitp)
              (retmsg "Splits are not supported in the test expression of ~
                       conditional expressions."))
             ((erp then?-splitp then?1 then?2 objs)
              (expr-option-peel
                expr.then struct-uid right-name right-set objs))
             ((erp else-splitp else1 else2 objs)
              (expr-peel expr.else struct-uid right-name right-set objs))
             ((unless (or then?-splitp else-splitp))
              (retok nil
                     (make-expr-cond :test test :then then?1 :else else1)
                     (irr-expr)
                     objs))
             ((unless (and then?-splitp else-splitp))
              (retmsg$ "Conditional expression can only be split if ~
                        both the \"then\" and \"else\" arguments are split.")))
          (retok t
                 (make-expr-cond :test test :then then?1 :else else1)
                 (make-expr-cond :test test :then then?2 :else else2)
                 objs))
        :comma
        (b* (((erp first-splitp first - objs)
              (expr-peel expr.first struct-uid right-name right-set objs))
             ((erp next-splitp next - objs)
              (expr-peel expr.next struct-uid right-name right-set objs))
             ((when (or first-splitp next-slitp))
              (retmsg$ "Splits are not supported in comma expressions.")))
          (retok nil
                 (make-expr-comma :first first :next next)
                 (irr-expr)
                 objs))
        :stmt
        ;; Assuming signature of stmt-peel
        (b* (((erp stmt objs)
              (stmt-peel expr.stmt struct-uid right-name right-set objs)))
          (retok nil
                 (expr-stmt stmt)
                 (irr-expr)
                 objs))
        :tycompat
        (b* (((erp tyname1-splitp tyname1 - objs)
              (tyname-peel
                expr.type1 struct-uid right-name right-set objs))
             ((erp tyname2-splitp tyname2 - objs)
              (tyname-peel
                expr.type2 struct-uid right-name right-set objs))
             ;; TODO: it may be possible to split such expressions.
             ((when (or tyname1-splitp tyname2-splitp))
              (retmsg$ "Splits are not supported in ~
                        __builtin-types_compatible_p expressions.")))
          (retok nil
                 (expr-tycompat :type1 tyname1 :type2 tyname2)
                 (irr-expr)
                 objs))
        ;; TODO GJ: This should get a direction from the member designator,
        ;;   to be used in the type name xform.
        :offsetof
        (b* (((erp tyname-splitp tyname - objs)
              (tyname-peel
                expr.type struct-uid right-name right-set objs))
             ((erp member-splitp member - objs)
              (member-designor-peel
                expr.member struct-uid right-name right-set objs))
             ;; TODO: consider whether it is possible to split such
             ;; expressions.
             ((when (or tyname-splitp member-splitp))
              (retmsg$ "Splits are not supported in ~
                        __builtin_offsetof expressions.")))
          (retok nil
                 (expr-offsetof :type tyname :member member)
                 (irr-expr)
                 objs))
        :va-arg
        (b* (((erp list-splitp list - objs)
              (expr-peel expr.list struct-uid right-name right-set objs))
             ((erp tyname-splitp tyname - objs)
              (tyname-peel
                expr.type struct-uid right-name right-set objs))
             ;; TODO: consider whether it is possible to split such
             ;; expressions.
             ((when (or list-splitp tyname-splitp))
              (retmsg$ "Splits are not supported in ~
                        __builtin_va_arg expressions.")))
          (retok nil
                 (expr-var-arg :list list :type tyname)
                 (irr-expr)
                 objs))
        :extension
        (b* (((erp splitp expr1 expr2 objs)
              (expr-peel
                expr.expr struct-uid right-name right-set objs)))
          (retok splitp
                 (expr-extension expr1)
                 (if splitp (expr-extension expr2) (irr-expr))
                 objs))
        :sizeof-ambig (retmsg$ "Ambiguous expressions are disallowed.")
        :alignof-ambig (retmsg$ "Ambiguous expressions are disallowed.")
        :cast/call-ambig (retmsg$ "Ambiguous expressions are disallowed.")
        :cast/mul-ambig (retmsg$ "Ambiguous expressions are disallowed.")
        :cast/add-ambig (retmsg$ "Ambiguous expressions are disallowed.")
        :cast/sub-ambig (retmsg$ "Ambiguous expressions are disallowed.")
        :cast/and-ambig (retmsg$ "Ambiguous expressions are disallowed.")
        :cast/logand-ambig (retmsg$ "Ambiguous expressions are disallowed.")))
    :measure (expr-count expr))

  ;; TODO GJ: come back to this after checking that we indeed always want a
  ;;   list of dirs.
  ;;   Although, now that I think about it, we may always want undirected.
  (define expr-list-peel
    ((exprs expr-listp)
     (objs uid-ident-mapp))
    :guard (and (expr-list-unambp exprs)
                (expr-list-annop exprs))
    :returns (result expr-listp)
    (if (endp exprs)
        nil
      (cons (expr-peel (car exprs) objs)
            (expr-list-peel (cdr exprs) objs)))
    :measure (expr-list-count exprs))

  (define expr-option-peel
    ((expr? expr-optionp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (expr-option-unambp expr?)
                (expr-option-annop expr?))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (expr1? expr-optionp)
                 (expr2? expr-optionp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) nil (expr-option-fix expr) nil objs))
      (expr-option-case
        expr?
        :some
        (b* (((erp splitp expr1 expr2 objs)
              (expr-peel expr?.val struct-uid right-name right-set objs)))
          (retok splitp
                 expr1
                 (if splitp expr2 nil)
                 objs))
        :none
        (retok nil nil nil objs)))
    :measure (expr-option-count expr?))

  (define const-expr-peel
    ((const-expr const-exprp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (const-expr-unambp const-expr)
                (const-expr-annop const-expr))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (const-expr1 const-exprp)
                 (const-expr2 const-exprp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) nil (expr-option-fix expr) nil objs)
         ((erp splitp expr1 expr2 objs)
          (expr-peel expr.expr struct-uid right-name right-set objs)))
      (retok splitp
             (const-expr expr1)
             (if splitp (const-expr expr2) (irr-const-expr))
             objs))
    :measure (const-expr-count const-expr))

  (define const-expr-option-peel
    ((const-expr? const-expr-optionp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (const-expr-option-unambp const-expr?)
                (const-expr-option-annop const-expr?))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (const-expr?1 const-expr-optionp)
                 (const-expr?2 const-expr-optionp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) nil (expr-option-fix expr) nil objs))
      (const-expr-option-case
        const-expr?
        :some
        (b* (((erp splitp const-expr1 const-expr2 objs)
              (const-expr-peel
                const-expr?.val struct-uid right-name right-set objs)))
          (retok splitp
                 const-expr1
                 (if splitp const-expr2 nil)
                 objs))
        :none
        (retok nil nil nil objs)))
    :measure (const-expr-option-count const-expr?))

  (define genassoc-peel
    ((genassoc genassocp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (genassoc-unambp genassoc)
                (genassoc-annop genassoc))
    :returns (mv (er? maybe-msgp)
                 (genassoc$ genassocp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (genassoc-fix genassoc) objs))
      (genassoc-case
        genassoc
        :type
        (b* (((erp tyname-splitp tyname - objs)
              (tyname-peel
                genassoc.type struct-uid right-name right-set (direction-both) objs))
             ((erp expr-splitp expr - objs)
              (expr-peel
                genassoc.expr struct-uid right-name right-set (direction-both) objs))
             ((when (or tyname-splitp expr-splitp))
              (retmsg$ "Splits are not supported in ~
                        generic associations expressions.")))
          (make-genassoc-type :type tyname :expr expr))
        :default
        (b* (((erp expr-splitp expr - objs)
              (expr-peel
                genassoc.expr struct-uid right-name right-set (direction-both) objs))
             ((when (or tyname-splitp expr-splitp))
              (retmsg$ "Splits are not supported in ~
                        generic associations expressions.")))
          (make-genassoc-default :expr expr))))
    :measure (genassoc-count genassoc))

  (define genassoc-list-peel
    ((genassocs genassoc-listp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (genassoc-list-unambp genassocs)
                (genassoc-list-annop genassocs))
    :returns (mv (er? maybe-msgp)
                 (genassocs$ genassoc-listp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (genassoc-list-fix genassocs) objs)
         ((when (endp genassocs))
          (retok nil objs))
         ((erp genassoc objs)
          (genassoc-peel
            (first genassocs) struct-uid right-name right-set objs))
         ((erp genassocs objs)
          (genassoc-list-peel
            (rest genassocs) struct-uid right-name right-set objs)))
      (retok (cons genassoc genassocs)
             objs))
    :measure (genassoc-list-count genassocs))

  ;; TODO GJ: This should never split, but it should probably return a direction.
  ;; - Actually, we could have a function outside the clique to get the direction.
  (define member-designor-peel
    ((member-designor member-designorp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (member-designor-unambp member-designor)
                (member-designor-annop member-designor))
    :returns (mv (er? maybe-msgp)
                 (member-designor$ member-designorp)
                 (objs$ uid-ident-mapp))
    (b* ((member-designor (member-designor-fix member-designor))
         (objs (uid-ident-map-fix objs))
         ((reterr) member-designor objs))
      (member-designor-case
        member-designor
        :ident
        (retok member-designor objs)
        :dot
        (b* (((erp member objs)
              (member-designor-peel
                member-designor.member struct-uid right-name right-set objs)))
          (retok (make-member-designor-dot :member member
                                           :name member-designor.name)
                 objs))
        :sub
        (b* (((erp member objs)
              (member-designor-peel
                member-designor.member struct-uid right-name right-set objs))
             ((erp splitp index - objs)
              (expr-peel
                member-designor.index struct-uid right-name right-set (direction-both) objs))
             ((when splitp)
              (retmsg$ "Splits are not supported in member designators.")))
          (retok (make-member-designor-sub :member member
                                           :index index)
                 objs))))
    :measure (member-designor-count member-designor))

  (define type-spec-peel
    ((type-spec type-specp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (type-spec-unambp type-spec)
                (type-spec-annop type-spec))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (type-spec1 type-specp)
                 (type-spec2 type-specp)
                 (objs$ uid-ident-mapp))
    (b* ((type-spec (type-spec-fix type-spec))
         (objs (uid-ident-map-fix objs))
         ((reterr) nil type-spec (irr-type-spec) objs))
      (type-spec-case
        type-spec
        :atomic
        (b* (((erp splitp tyname1 tyname2 objs)
              (tyname-peel
                type-spec.type struct-uid right-name right-set objs)))
          (retok splitp
                 (type-spec-atomic tyname1)
                 (if splitp (type-spec-atomic tyname1) (irr-type-spec))
                 objs))
        :struct
        (b* (((type-spec-struct-info info) type-spec.info)
             (splitp (c$::uid-equal info.uid struct-uid))
             ((erp spec1 spec2 objs)
              (struni-spec-peel
                type-spec.spec struct-uid right-name right-set splitp objs)))
          (retok splitp
                 (type-spec-struct spec1)
                 (if splitp (type-spec-struct spec2) (irr-type-spec))
                 objs))
        :union
        (b* (((erp spec - objs)
              (struni-spec-peel
                type-spec.spec struct-uid right-name right-set nil objs)))
          (retok nil
                 (type-spec-union spec)
                 (irr-type-spec)
                 objs))
        :enum
        (b* (((erp splitp spec - objs)
              (enum-spec-peel
                type-spec.spec struct-uid right-name right-set objs))
             ((when splitp)
              (retmsg$ "Splits are not supported in ~
                        enumeration type specifiers.")))
          (retok nil
                 (type-spec-union spec1)
                 (irr-type-spec)
                 objs))
        :struct-empty
        (b* (((erp attribs objs)
              (attrib-spec-list-peel
                type-spec.attribs struct-uid right-name right-set objs))
             ((type-spec-struct-info info) type-spec.info)
             (matchp (c$::uid-equal info.uid struct-uid)))
          (retok matchp
                 (change-type-spec-struct-empty type-spec :attribs attribs)
                 (if matchp
                     (change-type-spec-struct-empty
                       type-spec
                       :attribs attribs
                       :name? right-name)
                   (irr-type-spec))
                 objs))
        ;; TODO GJ: test this case.
        :typeof-expr
        (b* (((erp splitp expr1 expr2 objs)
              (expr-peel type-spec.expr struct-uid right-name right-set objs)))
          (retok splitp
                 (change-type-spec-typeof-expr type-spec :expr expr1)
                 (if slitp
                     (change-type-spec-typeof-expr type-spec :expr expr2)
                   (irr-type-spec))
                 objs))
        :typeof-type
        (b* (((erp splitp tyname1 tyname2 objs)
              (tyname-peel
                type-spec.type struct-uid right-name right-set objs)))
          (retok splitp
                 (change-type-spec-typeof-type type-spec :type tyname1)
                 (if slitp
                     (change-type-spec-typeof-type type-spec :type tyname2)
                   (irr-type-spec))
                 objs))
        :typeof-ambig (retmsg$ "Ambiguous type specifiers are disallowed.")
        :otherwise (retok nil type-spec (irr-type-spec) objs)))
    :measure (type-spec-count type-spec))

  (define spec/qual-peel
    ((spec/qual spec/qual-p)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (spec/qual-unambp spec/qual)
                (spec/qual-annop spec/qual))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (spec/qual1 spec/qual-p)
                 (spec/qual2 spec/qual-p)
                 (objs$ uid-ident-mapp))
    (b* ((spec/qual (spec/qual-fix spec/qual))
         (objs (uid-ident-map-fix objs))
         ((reterr) nil spec/qual (irr-spec/qual) objs))
      (spec/qual-case
        spec/qual
        :typespec
        (b* (((erp splitp type-spec1 type-spec2 objs)
              (type-spec-peel
                spec/qual.spec struct-uid right-name right-set objs)))
          (retok splitp
                 (spec/qual-typespec type-spec1)
                 (if splitp (spec/qual-typespec type-spec2) (irr-spec/qual))
                 objs))
        :typequal
        (retok nil
               (spec/qual-fix spec/qual)
               (irr-spec/qual)
               objs)
        :align
        (b* (((erp spec objs)
              (align-spec-peel
                spec/qual.spec struct-uid right-name right-set objs)))
          (retok nil
                 (spec/qual-align spec)
                 (irr-spec/qual)
                 objs))
        ;; GJ: Assuming here that attrib-spec-peel doesn't split
        :attrib
        (b* (((erp spec objs)
              (attrib-spec-peel
                spec/qual.spec struct-uid right-name right-set objs)))
          (retok nil
                 (spec/qual-attrib spec)
                 (irr-spec/qual)
                 objs))))
    :measure (spec/qual-count spec/qual))

  (define spec/qual-list-peel
    ((spec/quals spec/qual-listp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (spec/qual-list-unambp spec/quals)
                (spec/qual-list-annop spec/quals))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (spec/quals1 spec/qual-listp)
                 (spec/quals2 spec/qual-listp)
                 (objs$ uid-ident-mapp))
    (b* ((spec/quals (spec/qual-list-fix spec/quals))
         (objs (uid-ident-map-fix objs))
         ((reterr) nil spec/quals nil objs)
         ((erp first-splitp spec/qual1 spec/qual2 objs)
          (spec/qual-peel
            (first spec/quals) struct-uid right-name right-set objs))
         ((erp rest-splitp spec/quals1 spec/quals2 objs)
          (spec/qual-list-peel
            (rest spec/quals) struct-uid right-name right-set objs))
         (splitp (or first-splitp rest-splitp)))
      (retok splitp
             (cons spec/qual1 spec/quals1)
             (if first-splitp
                 (if rest-splitp
                     (cons spec/qual2 spec/quals2)
                   (cons spec/qual2 spec/quals1))
               (if rest-splitp
                   (cons spec/qual1 spec/quals2)
                 (cons spec/qual1 spec/quals1)))
             objs))
    :measure (spec/qual-list-count spec/quals))

  (define align-spec-peel
    ((align-spec align-specp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (align-spec-unambp align-spec)
                (align-spec-annop align-spec))
    :returns (mv (er? maybe-msgp)
                 (align-spec$ align-spec)
                 (objs$ uid-ident-mapp))
    (b* ((align-spec (align-spec-fix align-spec))
         (objs (uid-ident-map-fix objs))
         ((reterr) align-spec objs))
      (align-spec-case
        align-spec
        :alignas-type
        (b* (((erp splitp tyname - objs)
              (tyname-peel
                align-spec.tyname struct-uid right-name right-set objs))
             ((when splitp)
              (retmsg$ "Splits not allowed in align specifiers.")))
          (retok (align-spec-alignas-type tyname) objs))
        :alignas-expr
        (b* (((erp splitp expr - objs)
              (const-expr-peel
                align-spec.expr struct-uid right-name right-set objs))
             ((when splitp)
              (retmsg$ "Splits not allowed in align specifiers.")))
          (retok (align-spec-alignas-expr expr) objs))
        :alignas-ambig
        (retmsg$ "Ambiguous alignment specifiers are disallowed.")))
    :measure (align-spec-count align-spec))

  (define decl-spec-peel
    ((decl-spec decl-specp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (decl-spec-unambp decl-spec)
                (decl-spec-annop decl-spec))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (decl-spec1 decl-specp)
                 (decl-spec1 decl-specp)
                 (objs$ uid-ident-mapp))
    (b* ((decl-spec (decl-spec-fix decl-spec))
         (objs (uid-ident-map-fix objs))
         ((reterr) nil decl-spec (irr-decl-spec) objs))
      (decl-spec-case
        decl-spec
        :typespec
        (b* (((erp splitp spec1 spec2 objs)
              (type-spec-peel
                decl-spec.spec struct-uid right-name right-set objs)))
          (retok splitp
                 (decl-spec-typespec spec1)
                 (if splitp
                     (decl-spec-typespec spec2)
                   (irr-decl-spec))
                 objs))
        :align
        (b* (((erp spec objs)
              (align-spec-peel
                decl-spec.spec struct-uid right-name right-set objs)))
          (retok nil
                 (decl-spec-alignspec spec)
                 (irr-decl-spec)
                 objs))
        :attrib
        (b* (((erp spec objs)
              (attrib-spec-peel
                decl-spec.spec struct-uid right-name right-set objs)))
          (retok nil
                 (decl-spec-attribspec spec)
                 (irr-decl-spec)
                 objs))
        :otherwise
        (retok nil decl-spec (irr-decl-spec) objs))
    :measure (decl-spec-count decl-spec))

  (define decl-spec-list-peel
    ((decl-specs decl-spec-listp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (decl-spec-list-unambp decl-specs)
                (decl-spec-list-annop decl-specs))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (decl-specs1 decl-spec-listp)
                 (decl-specs2 decl-spec-listp)
                 (objs$ uid-ident-mapp))
    (b* ((decl-specs (decl-spec-list-fix decl-specs))
         (objs (uid-ident-map-fix objs))
         ((reterr) nil decl-specs nil objs)
         ((erp first-splitp decl-spec1 decl-spec2 objs)
          (decl-spec-peel
            (first decl-specs) struct-uid right-name right-set objs))
         ((erp rest-splitp decl-specs1 decl-specs2 objs)
          (decl-spec-list-peel
            (rest decl-specs) struct-uid right-name right-set objs))
         (splitp (or first-splitp rest-splitp)))
      (retok splitp
             (cons decl-spec1 decl-specs1)
             (if first-splitp
                 (if rest-splitp
                     (cons decl-spec2 decl-specs2)
                   (cons decl-spec2 decl-specs1))
               (if rest-splitp
                   (cons decl-spec1 decl-specs2)
                 (cons decl-spec1 decl-specs1)))
             objs))
    :measure (decl-spec-list-count decl-specs))

  (define typequal/attribspec-peel
    ((typequal/attribspec c$::typequal/attribspec-p)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (typequal/attribspec-unambp typequal/attribspec)
                (typequal/attribspec-annop typequal/attribspec))
    :returns (mv (er? maybe-msgp)
                 (typequal/attribspec$ typequal/attribspecp)
                 (objs$ uid-ident-mapp))
    (b* ((typequal/attribspec (typequal/attribspec-fix typequal/attribspec))
         (objs (uid-ident-map-fix objs))
         ((reterr) nil typequal/attribspec (irr-typequal/attribspec) objs))
      (c$::typequal/attribspec-case
        typequal/attribspec
        :type
        (retok typequal/attribspec objs)
        :attrib
        (b* (((erp spec objs)
              (attrib-spec-peel
                typequal/attribspec.spec struct-uid right-name right-set objs)))
          (retok (decl-spec-attribspec spec) objs))))
    :measure (c$::typequal/attribspec-count typequal/attribspec))

  (define typequal/attribspec-list-peel
    ((typequal/attribspecs c$::typequal/attribspec-listp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (typequal/attribspec-list-unambp typequal/attribspecs)
                (typequal/attribspec-list-annop typequal/attribspecs))
    :returns (mv (er? maybe-msgp)
                 (typequal/attribspecs$ typequal/attribspec-listp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (typequal/attribspec-list-fix typequal/attribspecs) objs)
         ((when (endp typequal/attribspecs))
          (retok nil objs))
         ((erp typequal/attribspec objs)
          (typequal/attribspec-peel
            (first typequal/attribspecs) struct-uid right-name right-set objs))
         ((erp typequal/attribspecs objs)
          (typequal/attribspec-list-peel
            (rest typequal/attribspecs) struct-uid right-name right-set objs)))
      (retok (cons typequal/attribspec typequal/attribspecs)
             objs))
    :measure (c$::typequal/attribspec-list-count typequal/attribspecs))

  (define typequal/attribspec-list-list-peel
    ((typequal/attribspec-lists typequal/attribspec-list-listp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (typequal/attribspec-list-list-unambp
                  typequal/attribspec-lists)
                (typequal/attribspec-list-list-annop
                  typequal/attribspec-lists))
    :returns (mv (er? maybe-msgp)
                 (typequal/attribspec-lists$ typequal/attribspec-list-listp)
                 (objs$ uid-ident-mapp))
    (b* ((typequal/attribspec-lists
           (typequal/attribspec-list-list-fix typequal/attribspec-lists))
         (objs (uid-ident-map-fix objs))
         ((reterr) typequal/attribspec-lists objs)
         ((when (endp typequal/attribspec-lists))
          (retok nil objs))
         ((erp typequal/attribspecs objs)
          (typequal/attribspec-list-peel
            (first typequal/attribspec-lists) struct-uid right-name right-set objs))
         ((erp typequal/attribspec-lists objs)
          (typequal/attribspec-list-list-peel
            (rest typequal/attribspec-lists) struct-uid right-name right-set objs)))
      (retok (cons typequal/attribspecs typequal/attribspec-lists)
             objs))
    :measure (c$::typequal/attribspec-list-list-count
              typequal/attribspec-lists))

  (define initer-peel
    ((initer initerp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (initer-unambp initer)
                (initer-annop initer))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (initer1 initerp)
                 (initer2 initerp)
                 (objs$ uid-ident-mapp))
    (b* ((initer (initer-fix initer))
         (objs (uid-ident-map-fix objs))
         ((reterr) nil initer (irr-initer) objs))
      (retmsg$ "Initializers are not yet supported.")
      ;; (initer-case
      ;;   initer
      ;;   :single
      ;;   (b* (((mv splitp expr1 expr2 objs)
      ;;         (expr-peel
      ;;           initer.expr struct-uid right-name right-set objs)))
      ;;     (retok splitp
      ;;            (initer-single expr1)
      ;;            (if splitp (initer-single expr2) (c$::irr-initer))
      ;;            objs))
      ;;   :list
      ;;   (b* (((mv splitp desiniters1 desiniters2 objs)
      ;;         (desiniter-list-peel
      ;;           initer.elems struct-uid right-name right-set objs)))
      ;;     (retok splitp
      ;;            (make-initer-list :elems elems1 :final-comma initer.final-comma)
      ;;            (if splitp
      ;;                (make-initer-list :elems elems2
      ;;                                  :final-comma initer.final-comma)
      ;;              (c$::irr-initer))
      ;;            objs)))
      )
    :measure (initer-count initer))

  (define initer-option-peel
    ((initer? initer-optionp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (initer-option-unambp initer?)
                (initer-option-annop initer?))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (initer?1 initer-optionp)
                 (initer?2 initer-optionp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) nil (initer-option-fix initer?) nil objs))
      (initer-option-case
        initer?
        :some
        (b* (((erp splitp initer1 initer2 objs)
              (initer-peel initer?.val struct-uid right-name right-set objs)))
          (retok splitp
                 initer1
                 (if splitp initer2 nil)
                 objs))
        :none
        (retok nil nil nil objs)))
    :measure (initer-option-count initer?))

  (define declor-peel
    ((declor declorp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (uid? c$::uid-optionp)
     (objs uid-ident-mapp))
    :guard (and (declor-unambp declor)
                (declor-annop declor))
    :returns (mv (er? maybe-msgp)
                 (declor1 declorp)
                 (declor2 declorp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (declor-fix declor) (c$::irr-declor) objs)
         ((erp pointers objs)
          (typequal/attribspec-peel
            declor.pointers struct-uid right-name right-set objs))
         ((erp direct1 direct2 objs)
          (dirdeclor-peel
            declor.direct struct-uid right-name right-set uid? objs)))
      (retok (make-declor :pointers declor.pointers :direct direct1)
             (if uid?
                 (make-declor :pointers declor.pointers :direct direct2)
               (c$::irr-declor))
             objs))
    :measure (declor-count declor))

  (define declor-option-peel
    ((declor? declor-optionp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (uid? c$::uid-optionp)
     (objs uid-ident-mapp))
    :guard (and (declor-option-unambp declor?)
                (declor-option-annop declor?))
    :returns (mv (er? maybe-msgp)
                 (declor?1 declor-optionp)
                 (declor?2 declor-optionp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (declor-option-fix declor?) nil objs))
      (declor-option-case
        declor?
        :some
        (b* (((erp declor1 declor2 objs)
              (declor-peel
                declor?.val struct-uid right-name right-set uid? objs)))
          (retok declor1
                 (if uid? declor2 nil)
                 objs))
        :none
        (retok nil nil objs)))
    :measure (declor-option-count declor?))

  (define dirdeclor-peel
    ((dirdeclor dirdeclorp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (uid? c$::uid-optionp)
     (objs uid-ident-mapp))
    :guard (and (dirdeclor-unambp dirdeclor)
                (dirdeclor-annop dirdeclor))
    :returns (mv (er? maybe-msgp)
                 (dirdeclor1 dirdeclorp)
                 (dirdeclor2 dirdeclorp)
                 (objs$ uid-ident-mapp))
    (b* ((dirdeclor (dirdeclor-fix dirdeclor))
         (objs (uid-ident-map-fix objs))
         ((reterr) dirdeclor nil objs))
      (dirdeclor-case
        dirdeclor
        :ident
        (b* (((unless uid?)
              (retok dirdeclor (irr-dirdeclor) objs))
             ((unless (stringp (ident->unwrap dirdeclor.ident)))
              (retmsg$ "Identifier is not a string."))
             ;; TODO: properly check for safety of this new identifier
             (ident-right (dirdeclor-ident
                            (concatenate 'string
                                         (ident->unwrap dirdeclor.ident)
                                         "__2"))))
          (retok dirdeclor
                 (dirdeclor-ident ident-right)
                 (omap::update uid? ident-right map)))
        :paren
        (b* (((erp inner1 inner2 objs)
              (declor-peel
                dirdeclor.inner struct-uid right-name right-set uid? objs)))
          (retok (dirdeclor-paren inner1)
                 (if uid?
                     (dirdeclor-paren inner2)
                   (irr-dirdeclor))
                 objs))
        :array
        (b* (((erp declor1 declor2 objs)
              (dirdeclor-peel
                dirdeclor.declor struct-uid right-name right-set uid? objs))
             ((erp qualspecs objs)
              (typequal/attribspec-peel
                dirdeclor.qualspecs struct-uid right-name right-set objs))
             ((erp size?-splitp size? - objs)
              (expr-option-peel
                dirdeclor.size? struct-uid right-name right-set objs))
             ((when size?-splitp)
              (retmsg$ "splits not allowed in array sizes.")))
          (retok (make-dirdeclor-array
                   :declor declor1
                   :qualspecs qualspecs
                   :size? size?)
                 (if uid?
                     (make-dirdeclor-array
                       :declor declor2
                       :qualspecs qualspecs
                       :size? size?)
                   (irr-dirdeclor))
                 objs))
        :array-static1
        (b* (((erp declor1 declor2 objs)
              (dirdeclor-peel
                dirdeclor.declor struct-uid right-name right-set uid? objs))
             ((erp qualspecs objs)
              (typequal/attribspec-peel
                dirdeclor.qualspecs struct-uid right-name right-set objs))
             ((erp size-splitp size - objs)
              (expr-peel dirdeclor.size struct-uid right-name right-set objs))
             ((when size-splitp)
              (retmsg$ "splits not allowed in array sizes.")))
          (retok (make-dirdeclor-array-static1
                   :declor declor1
                   :qualspecs qualspecs
                   :size? size?)
                 (if uid?
                     (make-dirdeclor-array-static1
                       :declor declor2
                       :qualspecs qualspecs
                       :size? size?)
                   (irr-dirdeclor))
                 objs))
        :array-static2
        (b* (((erp declor1 declor2 objs)
              (dirdeclor-peel
                dirdeclor.declor struct-uid right-name right-set uid? objs))
             ((erp qualspecs objs)
              (typequal/attribspec-peel
                dirdeclor.qualspecs struct-uid right-name right-set objs))
             ((erp size-splitp size - objs)
              (expr-peel dirdeclor.size struct-uid right-name right-set objs))
             ((when size-splitp)
              (retmsg$ "splits not allowed in array sizes.")))
          (retok (make-dirdeclor-array-static2
                   :declor declor1
                   :qualspecs qualspecs
                   :size? size?)
                 (if uid?
                     (make-dirdeclor-array-static2
                       :declor declor2
                       :qualspecs qualspecs
                       :size? size?)
                   (irr-dirdeclor))
                 objs))
        :array-star
        (b* (((erp declor1 declor2 objs)
              (dirdeclor-peel
                dirdeclor.declor struct-uid right-name right-set uid? objs))
             ((erp qualspecs objs)
              (typequal/attribspec-peel
                dirdeclor.qualspecs struct-uid right-name right-set objs)))
          (retok (make-dirdeclor-array-star
                   :declor declor1
                   :qualspecs qualspecs)
                 (if uid?
                     (make-dirdeclor-array-star
                       :declor declor2
                       :qualspecs qualspecs)
                   (irr-dirdeclor))
                 objs))
        :function-params
        (b* (((erp declor1 declor2 objs)
              (dirdeclor-peel
                dirdeclor.declor struct-uid right-name right-set uid? objs))
             ((erp params objs)
              (param-declon-list-peel
                dirdeclor.params struct-uid right-name right-set objs)))
          (retok (make-dirdeclor-function-params
                   :declor declor1
                   :params params
                   :ellipsis dirdeclor.ellipsis)
                 (if uid?
                     (make-dirdeclor-function-params
                       :declor declor2
                       :params params
                       :ellipsis dirdeclor.ellipsis)
                   (irr-dirdeclor))
                 objs))
        :function-names
        (b* (((erp declor1 declor2 objs)
              (dirdeclor-peel
                dirdeclor.declor struct-uid right-name right-set uid? objs)))
          (retok (make-dirdeclor-function-names
                   :declor declor1
                   :names dirdeclor.names)
                 (if uid?
                     (make-dirdeclor-function-names
                       :declor declor2
                       :names dirdeclor.names)
                   (irr-dirdeclor))
                 objs))))
    :measure (dirdeclor-count dirdeclor))

  (define absdeclor-peel
    ((absdeclor declorp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (splitp booleanp)
     (objs uid-ident-mapp))
    :guard (and (absdeclor-unambp absdeclor)
                (absdeclor-annop absdeclor))
    :returns (mv (er? maybe-msgp)
                 (absdeclor1 absdeclorp)
                 (absdeclor2 absdeclorp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (absdeclor-fix absdeclor) (c$::irr-absdeclor) objs)
         ((erp pointers objs)
          (typequal/attribspec-peel
            declor.pointers struct-uid right-name right-set objs))
         ((erp direct?1 direct?2 objs)
          (dirabsdeclor-option-peel
            absdeclor.direct? struct-uid right-name right-set splitp objs)))
      (retok (make-absdeclor :pointers absdeclor.pointers :direct? direct?1)
             (if splitp
                 (make-absdeclor :pointers absdeclor.pointers
                                 :direct? direct?2)
               (c$::irr-absdeclor))
             objs))
    :measure (absdeclor-count absdeclor))

  (define absdeclor-option-peel
    ((absdeclor? absdeclor-optionp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (splitp booleanp)
     (objs uid-ident-mapp))
    :guard (and (absdeclor-option-unambp absdeclor?)
                (absdeclor-option-annop absdeclor?))
    :returns (mv (er? maybe-msgp)
                 (absdeclor?1 absdeclor-optionp)
                 (absdeclor?2 absdeclor-optionp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (absdeclor-option-fix absdeclor?) nil objs))
      (absdeclor-option-case
        absdeclor?
        :some
        (b* (((erp absdeclor1 absdeclor2 objs)
              (absdeclor-peel
                absdeclor?.val struct-uid right-name right-set splitp objs)))
          (retok absdeclor1
                 (if splitp absdeclor2 nil)
                 objs))
        :none
        (retok nil nil objs)))
    :measure (absdeclor-option-count absdeclor?))

  (define dirabsdeclor-peel
    ((dirabsdeclor dirabsdeclorp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (uid? c$::uid-optionp)
     (objs uid-ident-mapp))
    :guard (and (dirabsdeclor-unambp dirabsdeclor)
                (dirabsdeclor-annop dirabsdeclor))
    :returns (mv (er? maybe-msgp)
                 (dirabsdeclor1 dirabsdeclorp)
                 (dirabsdeclor2 dirabsdeclorp)
                 (objs$ uid-ident-mapp))
    (b* ((dirabsdeclor (dirabsdeclor-fix dirdeclor))
         (objs (uid-ident-map-fix objs))
         ((reterr) dirabsdeclor nil objs))
      (dirabsdeclor-case
        dirabsdeclor
        :dummy-base
        (retok dirabsdeclor (c$::irr-dirabsdeclor) objs)
        :paren
        (b* (((erp inner1 inner2 objs)
              (absdeclor-peel
                dirabsdeclor.inner struct-uid right-name right-set splitp objs)))
          (retok (dirabsdeclor-paren inner1)
                 (if splitp
                     (dirabsdeclor-paren inner2)
                   (irr-dirabsdeclor))
                 objs))
        :array
        (b* (((erp declor?1 declor?2 objs)
              (dirabsdeclor-option-peel
                dirdeclor.declor? struct-uid right-name right-set splitp objs))
             ((erp qualspecs objs)
              (typequal/attribspec-peel
                dirabsdeclor.qualspecs struct-uid right-name right-set objs))
             ((erp size?-splitp size? - objs)
              (expr-option-peel
                dirabsdeclor.size? struct-uid right-name right-set objs))
             ((when size?-splitp)
              (retmsg$ "splits not allowed in array sizes.")))
          (retok (make-dirabsdeclor-array
                   :declor? declor?1
                   :qualspecs qualspecs
                   :size? size?)
                 (if splitp
                     (make-dirabsdeclor-array
                       :declor? declor?2
                       :qualspecs qualspecs
                       :size? size?)
                   (irr-dirabsdeclor))
                 objs))
        :array-static1
        (b* (((erp declor?1 declor?2 objs)
              (dirabsdeclor-option-peel
                dirabsdeclor.declor? struct-uid right-name right-set splitp objs))
             ((erp qualspecs objs)
              (typequal/attribspec-peel
                dirabsdeclor.qualspecs struct-uid right-name right-set objs))
             ((erp size-splitp size - objs)
              (expr-peel dirabsdeclor.size struct-uid right-name right-set objs))
             ((when size-splitp)
              (retmsg$ "splits not allowed in array sizes.")))
          (retok (make-dirbsdeclor-array-static1
                   :declor? declor?1
                   :qualspecs qualspecs
                   :size? size?)
                 (if splitp
                     (make-dirabsdeclor-array-static1
                       :declor? declor?2
                       :qualspecs qualspecs
                       :size? size?)
                   (irr-dirabsdeclor))
                 objs))
        :array-static2
        (b* (((erp declor?1 declor?2 objs)
              (dirabsdeclor-option-peel
                dirabsdeclor.declor struct-uid right-name right-set splitp objs))
             ((erp qualspecs objs)
              (typequal/attribspec-peel
                dirabsdeclor.qualspecs struct-uid right-name right-set objs))
             ((erp size-splitp size - objs)
              (expr-peel
                dirabsdeclor.size struct-uid right-name right-set objs))
             ((when size-splitp)
              (retmsg$ "splits not allowed in array sizes.")))
          (retok (make-dirabsdeclor-array-static2
                   :declor? declor?1
                   :qualspecs qualspecs
                   :size? size?)
                 (if splitp
                     (make-dirabsdeclor-array-static2
                       :declor? declor?2
                       :qualspecs qualspecs
                       :size? size?)
                   (irr-dirabsdeclor))
                 objs))
        :array-star
        (b* (((erp declor?1 declor?2 objs)
              (dirabsdeclor-option-peel
                dirdeclor.declor? struct-uid right-name right-set splitp objs)))
          (retok (make-dirabsdeclor-array-star :declor? declor?1)
                 (if splitp
                     (make-dirabsdeclor-array-star :declor? declor?2)
                   (irr-dirdeclor))
                 objs))
        :function
        (b* (((erp declor?1 declor?2 objs)
              (dirabsdeclor-peel
                dirabsdeclor.declor? struct-uid right-name right-set splitp objs))
             ((erp params objs)
              (param-declon-list-peel
                dirdeclor.params struct-uid right-name right-set objs)))
          (retok (make-dirabsdeclor-function
                   :declor? declor?1
                   :params params
                   :ellipsis dirdeclor.ellipsis)
                 (if splituid?
                     (make-dirabsdeclor-function
                       :declor? declor?2
                       :params params
                       :ellipsis dirdeclor.ellipsis)
                   (irr-dirabsdeclor))
                 objs))))
    :measure (dirabsdeclor-count dirabsdeclor))

  (define dirabsdeclor-option-peel
    ((dirabsdeclor? dirabsdeclor-optionp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (splitp booleanp)
     (objs uid-ident-mapp))
    :guard (and (dirabsdeclor-option-unambp dirabsdeclor?)
                (dirabsdeclor-option-annop dirabsdeclor?))
    :returns (mv (er? maybe-msgp)
                 (dirabsdeclor?1 dirabsdeclor-optionp)
                 (dirabsdeclor?2 dirabsdeclor-optionp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (dirabsdeclor-option-fix dirabsdeclor?) nil objs))
      (dirabsdeclor-option-case
        dirabsdeclor?
        :some
        (b* (((erp dirabsdeclor1 dirabsdeclor2 objs)
              (dirabsdeclor-peel
                dirabsdeclor?.val struct-uid right-name right-set splitp objs)))
          (retok dirabsdeclor1
                 (if splitp dirabsdeclor2 nil)
                 objs))
        :none
        (retok nil nil objs)))
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  (define param-declon-peel
    ((param-declon param-declonp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (param-declon-unambp param-declon)
                (param-declon-annop param-declon))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (param-declon1 param-declonp)
                 (param-declon2 param-declonp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) nil (param-declon-fix param-declon) (irr-param-declon) objs)
         ((param-declon-info info) param-declon.info)
         ((erp uid?)
          (b* (((reterr) nil))
            (type-case
              info.type
              :struct (retok (and (c$::uid-equal info.type.uid struct-uid)
                                  struct-uid))
              :unknown ;; TODO: If we had the full set of struct names handy,
                       ;;   we could determine that many such cases are safe
                       ;;   (when the name is not a member of the set).
                       (retmsg$ "Cannot transform parameter declaration ~
                                 of unknown type.")
              :otherwise (retok nil))))
         ((erp specs-splitp specs1 specs2 objs)
          (decl-spec-list-peel
            param-declon.specs struct-uid right-name right-set objs))
         ((erp declor declor2 objs)
          (param-declor-peel
            param-declon.declor struct-uid right-name right-set uid? objs))
         ((when (and uid? (not specs-splitp)))
          (retmsg$ "Internal error: param-declor split, ~
                    but decl-specs didn't."))
         ((erp attribs objs)
          (attrib-spec-list-peel
            param-declon.attribs struct-uid right-name right-set objs)))
      (retok specs-splitp
             (make-param-declon
               :specs specs1
               :declor declor1
               :attribs attribs)
             (if specs-splitp
                 (make-param-declon
                   :specs specs2
                   :declor (if uid? declor2 declor1)
                   :attribs attribs)
               (irr-param-declon))
             objs))
    :measure (param-declon-count param-declon))

  (define param-declon-list-peel
    ((param-declons param-declon-listp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (param-declon-list-unambp param-declons)
                (param-declon-list-annop param-declons))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (param-declons$ param-declon-listp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) nil (param-declon-fix param-declon) objs)
         ((erp first-splitp declon1 declon2 objs)
          (param-declon-peel
            (first param-declons) struct-uid right-name right-set objs))
         ((erp rest-splitp declons objs)
          (param-declon-list-peel
            (rest param-declons) struct-uid right-name right-set objs)))
      (retok (or first-splitp rest-splitp)
             (cons declon1
                   (if first-splitp
                       (cons declon2 declons)
                     declons))
             objs))
    :measure (param-declon-list-count param-declons))

  (define param-declor-peel
    ((param-declor param-declorp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (uid? c$::uid-optionp)
     (objs uid-ident-mapp))
    :guard (and (param-declor-unambp param-declor)
                (param-declor-annop param-declor))
    :returns (mv (er? maybe-msgp)
                 (param-declor1 param-declorp)
                 (param-declor2 param-declorp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (param-declor-fix param-declor) (irr-param-declor) objs))
      (param-declor-case
        param-declor
        :nonabstract
        (b* (((erp declor1 declor2 objs)
              (declor-peel
                param-declor.declor struct-uid right-name right-set uid? objs)))
          (retok (make-param-declor-nonabstract :declor declor1)
                 (if uid?
                     (make-param-declor-nonabstract :declor declor2)
                   (irr-param-declor))
                 objs))
        :abstract
        (b* (((erp absdeclor1 absdeclor2 objs)
              (absdeclor-peel
                param-declor.declor struct-uid right-name right-set (and uid? t) objs)))
          (retok (make-param-declor-abstract :declor absdeclor1)
                 (if uid?
                     (make-param-declor-abstract :declor absdeclor2)
                   (irr-param-declor))
                 objs))
        :none
        (if uid?
            (retmsg$ "Splits are not yet supported ~
                      in empty parameter declarators.")
          (retok (param-declor-fix param-declor)))
        :ambig
        (retmsg$ "Ambiguous parameter declarators are disallowed.")))
    :measure (param-declor-count param-declor))

  (define tyname-peel
    ((tyname tynamep)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (uid? c$::uid-optionp)
     (objs uid-ident-mapp))
    :guard (and (tyname-unambp tyname)
                (tyname-annop tyname))
    :returns (mv (er? maybe-msgp)
                 (splitp booleanp)
                 (tyname1 tynamep)
                 (tyname2 tynamep)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (tyname-fix tyname) (c$::irr-tyname) objs)
         ((tyname tyname) tyname)
         ((erp specquals-splitp specquals1 specquals2 objs)
          (spec/qual-list-peel
            tyname.specquals struct-uid right-name right-set objs))
         ((erp absdeclor?-splitp absdeclor?1 absdeclor?2 objs)
          (absdeclor-option-peel
            tyname.declor? struct-uid right-name right-set objs))
         ;; TODO: should the absdeclor? ever split? I'm thinking perhaps not.
         ((when absdeclor?-splitp)
          (retmsg$ "Splits are not supported ~
                    in the abstract declarator of a type name.")))
      (retok specquals-splitp
             (make-tyname :specquals specquals1 :declor? absdeclor?1)
             (if specquals-splitp
                 (make-tyname :specquals specquals2 :declor? absdeclor?1)
               (c$::irr-tyname))
             objs))
    :measure (tyname-count tyname))

  (define struni-spec-peel
    ((struni-spec struni-specp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (splitp booleanp)
     (objs uid-ident-mapp))
    :guard (and (struni-spec-unambp struni-spec)
                (struni-spec-annop struni-spec))
    :returns (mv (er? maybe-msgp)
                 (struni-spec1 struni-specp)
                 (struni-spec2 struni-specp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (struni-spec-fix struni-spec) (c$::irr-struni-spec) objs)
         ((struni-spec struni-spec) struni-spec)
         ((erp attribs objs)
          (attrib-spec-list-peel
            struni-spec.attribs struct-uid right-name right-set objs))
         ((erp members1 members2 objs)
          (struct-declon-list-peel
            struni-spec.members struct-uid right-name right-set splitp objs)))
      (retok (make-struni-spec :attribs attribs
                               :name struni-spec.name?
                               :members members1)
             (if splitp
                 (make-struni-spec :attribs attribs
                                   :name right-name
                                   :members members2)
               (c$::irr-struni-spec))
             objs))
    :measure (struni-spec-count struni-spec))

  (define struct-declon-peel
    ((struct-declon struct-declonp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (splitp booleanp)
     (objs uid-ident-mapp))
    :guard (and (struct-declon-unambp struct-declon)
                (struct-declon-annop struct-declon))
    :returns (mv (er? maybe-msgp)
                 (struct-declon?1 struct-declon-optionp)
                 (struct-declon?2 struct-declon-optionp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (struct-declon-fix struct-declon) nil objs))
      (struct-declon-case
        struct-declon
        :member
        (b* (((erp specquals-splitp specquals - objs)
              (spec/qual-list-peel
                struct-declon.specquals struct-uid right-name right-set objs))
             ((when specquals-splitp)
              (retmsg$ "Splits are not supported in structure declarations."))
             ((erp declors objs)
              (struct-declor-list-peel
                struct-declon.declors struct-uid right-name right-set objs))
             ((erp attribs objs)
              (attrib-spec-list
                struct-declon.attribs struct-uid right-name right-set objs))
             ((unless splitp)
              (retok (make-struct-declon-member
                       :extension struct-declon.extension
                       :specquals specquals
                       :declors declors
                       :attribs attribs)
                     (c$::irr-struct-declon)
                     objs))
             ((mv declors-left declors-right)
              ;; TODO: can this ever be a problem? What about bit fields?
              (split-struct-declors right-set declors))
             (struct-declon?1
               (if declors-left
                   (make-struct-declon-member
                     :extension struct-declon.extension
                     :specquals specquals
                     :declors declors-left
                     :attribs attribs)
                 nil))
             (struct-declon?2
               (if declors-left
                   (make-struct-declon-member
                     :extension struct-declon.extension
                     :specquals specquals
                     :declors declors-right
                     :attribs attribs)
                 nil)))
          (retok struct-declon?1
                 struct-declon?2
                 objs))
        :statassert
        (b* (((when splitp)
              (retmsg$ "Splits are not supported in ~
                        a struct declaration list when ~
                        static assertions are present."))
             ((erp statassert objs)
              (statassert-peel
                struct-declon.statassert struct-uid right-name right-set objs)))
          (retok (struct-declon-statassert statassert)
                 nil
                 objs))
        :empty
        (retok (struct-declon-empty)
               nil
               objs)))
    :measure (struct-declon-count struct-declon))

  (define struct-declon-list-peel
    ((struct-declons struct-declon-listp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (splitp booleanp)
     (objs uid-ident-mapp))
    :guard (and (struct-declon-list-unambp struct-declon-list)
                (struct-declon-list-annop struct-declon-list))
    :returns (mv (er? maybe-msgp)
                 (struct-declons1 struct-declon-listp)
                 (struct-declons1 struct-declon-listp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (struct-declon-list-fix struct-declons) nil objs)
         ((when (endp struct-declons))
          (retok nil nil objs))
         ((erp struct-declon1? struct-declon2? objs)
          (struct-declon-peel
            (first struct-declons) struct-uid right-name right-set splitp objs))
         ((erp struct-declons1 struct-declons2 objs)
          (struct-declon-list-peel
            (rest struct-declons) struct-uid right-name right-set splitp objs)))
      (retok (if struct-declon1?
                 (cons struct-declon1? struct-declons1)
               struct-declons1)
             (if struct-declon2?
                 (cons struct-declon2? struct-declons2)
               struct-declons2)
             objs))
    :measure (struct-declon-list-count struct-declons))

  (define struct-declor-peel
    ((struct-declor struct-declorp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (struct-declor-unambp struct-declor)
                (struct-declor-annop struct-declor))
    :returns (mv (er? maybe-msgp)
                 (struct-declor$ struct-declorp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (struct-declor-fix struct-declor) (c$::irr-struct-declor) objs)
         ((struct-declor struct-declor) struct-declor)
         ((struct-declor-info info) struct-declor.info)
         ((when (type-case
                  info.type
                  :struct (c$::uid-equal info.type.uid struct-uid)
                  :otherwise nil))
          (retmsg$ "Splits are not yet supported in struct declarators."))
         ((erp declor?$ - objs)
          (declor-option-peel
            struct-declor.declor? struct-uid right-name right-set nil objs))
         ((erp expr?-splitp expr?$ - objs)
          (cons-expr-option-peel
            struct-declor.expr? struct-uid right-name right-set nil objs))
         ((when expr?-splitp)
          (retmsg$ "Splits are not yet supported in struct declarators.")))
      (retok (make-struct-declor :declor? declor?$ :expr? expr?$)
             objs))
    :measure (struct-declor-count struct-declor))

  (define struct-declor-list-peel
    ((struct-declors struct-declor-listp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (struct-declor-list-unambp struct-declors)
                (struct-declor-list-annop struct-declors))
    :returns (mv (er? maybe-msgp)
                 (struct-declors$ struct-declor-listp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr)
          (struct-declor-list-fix struct-declors)
          (c$::irr-struct-declor-list)
          objs)
         ((when (endp struct-declors))
          (retok nil objs))
         ((erp struct-declor objs)
          (struct-declor-peel
            (first struct-declors) struct-uid right-name right-set objs))
         ((erp struct-declors$ objs)
          (struct-declor-list-peel
            (rest struct-declors) struct-uid right-name right-set objs)))
      (retok (cons struct-declor struct-declors$)
             objs))
    :measure (struct-declor-list-count struct-declor-list))

  (define enum-spec-peel
    ((enum-spec enum-specp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (enum-spec-unambp enum-spec)
                (enum-spec-annop enum-spec))
    :returns (mv (er? maybe-msgp)
                 (enum-spec$ enum-specp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (enum-spec-fix enum-sepc) (c$::irr-enum-spec) objs)
         ((enum-spec enum-spec) enum-spec)
         ((erp enumer-list objs)
          (enumer-list-peel
            enum-spec.enumers struct-uid right-name right-set objs)))
      (retok (make-enum-spec :name? enum-spec.name?
                             :enumers enumer-list
                             :final-comma enum-spec.final-comma)
             objs))
    :measure (enum-spec-count enum-spec))

  (define enumer-peel
    ((enumer enumerp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (enumer-unambp enumer)
                (enumer-annop enumer))
    :returns (mv (er? maybe-msgp)
                 (enumer$ enumerp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (enumer-fix enumer) (c$::irr-enumer) objs)
         ((enumer enumer) enumer)
         ((erp splitp value? - objs)
          (const-expr-option-peel
            enumer.value? struct-uid right-name right-set objs))
         ((when splitp)
          (retmsg$ "Splits are not supported in enumerators.")))
      (retok (make-enumer :name enumer.name :value? value?)
             objs))
    :measure (enumer-count enumer))

  (define enumer-list-peel
    ((enumers enumer-listp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (enumer-list-unambp enumers)
                (enumer-list-annop enumers))
    :returns (mv (er? maybe-msgp)
                 (enumers$ enumer-listp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (enumer-list-fix enumers) nil objs)
         ((erp enumer objs)
          (enumer-peel (first enumers) struct-uid right-name right-set objs))
         ((erp enumers$ objs)
          (enumer-list-peel
            (rest enumers) struct-uid right-name right-set objs)))
      (retok (cons enumer enumers$)
             objs))
    :measure (enumer-list-count enumers))

  (define statassert-peel
    ((statassert statassertp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (statassert-unambp statassert)
                (statassert-annop statassert))
    :returns (mv (er? maybe-msgp)
                 (statassert$ statassertp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (statassert-fix statassert) (c$::irr-statassert) objs)
         ((statassert statassert) statassert)
         ((erp splitp test - objs)
          (const-expr-peel
            statassert.test struct-uid right-name right-set objs))
         ((when splitp)
          (retmsg$ "Splits are not supported in ~
                    static assertion declarations.")))
      (retok (make-statassert :test test :message statassert.message)
             objs))
    :measure (statassert-count statassert))

  (define attrib-peel
    ((attrib c$::attribp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (c$::attrib-unambp attrib)
                (c$::attrib-annop attrib))
    :returns (mv (er? maybe-msgp)
                 (attrib$ c$::attribp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (c$::attrib-fix attrib) (c$::irr-attrib) objs))
      (c$::attrib-case
     attrib
     :name
     (retok (c$::attrib-fix attrib)
            objs)
     :name-params
     ;; TODO: here, we are assuming that expr-list-peel splits by duplicating
     ;; inline, and that it will return a splitp if anything has split. In this
     ;; case, the splitp is necessary to produce an error.
     (b* (((erp splitp params objs)
           (expr-list-peel attrib.params struct-uid right-name right-set objs))
          ((when splitp)
           (retmsg$ "Splits are not supported in attributes.")))
       (retok (c$::make-attrb-name-params :name attrib.name :params params)
              objs))))
    :measure (c$::attrib-count attrib))

  (define attrib-list-peel
    ((attribs c$::attrib-listp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (c$::attrib-list-unambp attribs)
                (c$::attrib-list-annop attribs))
    :returns (mv (er? maybe-msgp)
                 (attribs$ c$::attrib-listp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (c$::attrib-list-fix enumers) nil objs)
         ((erp attrib objs)
          (attrib-peel (first attribs) struct-uid right-name right-set objs))
         ((erp attribs$ objs)
          (attrib-list-peel
            (rest attribs) struct-uid right-name right-set objs)))
      (retok (cons attrib attribs$)
             objs))
    :measure (c$::attrib-list-count attribs))

  (define attrib-spec-peel
    ((attrib-spec c$::attrib-specp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (c$::attrib-spec-unambp attrib-spec)
                (c$::attrib-spec-annop attrib-spec))
    :returns (mv (er? maybe-msgp)
                 (attrib-spec$ c$::attrib-specp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr)
          (c$::attrib-spec-fix attrib-spec) (c$::irr-attrib-spec) objs)
         ((attrib-spec attrib-spec) attrib-spec)
         ((erp attribs objs)
          (attrib-list-peel
            attrib-spec.attribs struct-uid right-name right-set objs)))
      (retok (c$::make-attribs :uscores attrib-spec.uscores :attribs attribs)
             objs))
    :measure (c$::attrib-spec-count attrib-spec))

  (define attrib-spec-list-peel
    ((attrib-specs c$::attrib-spec-listp)
     (struct-uid uidp)
     (right-name identp)
     (right-set ident-setp)
     (objs uid-ident-mapp))
    :guard (and (c$::attrib-spec-list-unambp attrib-specs)
                (c$::attrib-spec-list-annop attrib-specs))
    :returns (mv (er? maybe-msgp)
                 (attribs$ c$::attrib-spec-listp)
                 (objs$ uid-ident-mapp))
    (b* ((objs (uid-ident-map-fix objs))
         ((reterr) (c$::attrib-spec-list-fix enumers) nil objs)
         ((erp attrib-spec objs)
          (attrib-spec-peel
            (first attrib-specs) struct-uid right-name right-set objs))
         ((erp attrib-specs$ objs)
          (attrib-spec-list-peel
            (rest attrib-specs) struct-uid right-name right-set objs)))
      (retok (cons attrib-spec attrib-specs$)
             objs))
    :measure (c$::attrib-spec-list-count attrib-specs))

  ;; GJ resume here
  (define init-declor-peel ((init-declor init-declorp)
                            (objs uid-ident-mapp))
    :returns (result init-declorp)
    (init-declor
     (declor-peel (init-declor->declor init-declor)
                  objs)
     (c$::init-declor->asm? init-declor)
     (attrib-spec-list-peel
       (c$::init-declor->attribs init-declor)
       objs)
     (initer-option-peel (init-declor->initer? init-declor)
                         objs)
     (c$::init-declor->info init-declor))
    :measure (init-declor-count init-declor))

  (define init-declor-list-peel
    ((init-declor-list init-declor-listp)
     (objs uid-ident-mapp))
    :returns (result init-declor-listp)
    (if (endp init-declor-list)
        nil
      (cons (init-declor-peel (car init-declor-list)
                              objs)
            (init-declor-list-peel (cdr init-declor-list)
                                   objs)))
    :measure (init-declor-list-count init-declor-list))

  (define declon-peel ((declon declonp)
                       (objs uid-ident-mapp))
    :returns (result declonp)
    (declon-case
     declon
     :declon
     (declon-declon
       (declon-declon->extension declon)
       (decl-spec-list-peel (declon-declon->specs declon)
                            objs)
       (init-declor-list-peel (declon-declon->declors declon)
                              objs))
     :statassert
     (declon-statassert (statassert-peel
                          (c$::declon-statassert->statassert declon)
                           objs)))
    :measure (declon-count declon))

  (define declon-list-peel ((declon-list declon-listp)
                            (objs uid-ident-mapp))
    :returns (result declon-listp)
    (if (endp declon-list)
        nil
      (cons (declon-peel (car declon-list)
                          objs)
            (declon-list-peel (cdr declon-list)
                               objs)))
    :measure (declon-list-count declon-list))

  (define label-peel ((label labelp)
                      (objs uid-ident-mapp))
    :returns (result labelp)
    (label-case
     label
     :name (c$::label-name (c$::label-name->name label)
                           (attrib-spec-list-peel
                             (c$::label-name->attribs label)
                             objs))
     :casexpr
     (c$::label-casexpr
       (const-expr-peel (c$::label-casexpr->expr label)
                        objs)
       (const-expr-option-peel
         (c$::label-casexpr->range? label)
         objs))
     :default (label-fix label))
    :measure (label-count label))

  (define asm-output-peel ((asm-output c$::asm-outputp)
                           (objs uid-ident-mapp))
    :returns (result c$::asm-outputp)
    (c$::asm-output
     (c$::asm-output->name? asm-output)
     (c$::asm-output->constraint asm-output)
     (expr-peel (c$::asm-output->lvalue asm-output)
                objs))
    :measure (c$::asm-output-count asm-output))

  (define asm-output-list-peel
    ((asm-output-list c$::asm-output-listp)
     (objs uid-ident-mapp))
    :returns (result c$::asm-output-listp)
    (if (endp asm-output-list)
        nil
      (cons (asm-output-peel (car asm-output-list)
                             objs)
            (asm-output-list-peel (cdr asm-output-list)
                                  objs)))
    :measure (c$::asm-output-list-count asm-output-list))

  (define asm-input-peel ((asm-input c$::asm-inputp)
                          (objs uid-ident-mapp))
    :returns (result c$::asm-inputp)
    (c$::asm-input
     (c$::asm-input->name? asm-input)
     (c$::asm-input->constraint asm-input)
     (expr-peel (c$::asm-input->rvalue asm-input)
                objs))
    :measure (c$::asm-input-count asm-input))

  (define asm-input-list-peel
    ((asm-input-list c$::asm-input-listp)
     (objs uid-ident-mapp))
    :returns (result c$::asm-input-listp)
    (if (endp asm-input-list)
        nil
      (cons (asm-input-peel (car asm-input-list)
                            objs)
            (asm-input-list-peel (cdr asm-input-list)
                                 objs)))
    :measure (c$::asm-input-list-count asm-input-list))

  (define asm-stmt-peel ((asm-stmt c$::asm-stmtp)
                         (objs uid-ident-mapp))
    :returns (result c$::asm-stmtp)
    (c$::asm-stmt
     (c$::asm-stmt->uscores asm-stmt)
     (c$::asm-stmt->quals asm-stmt)
     (c$::asm-stmt->template asm-stmt)
     (c$::asm-stmt->num-colons asm-stmt)
     (asm-output-list-peel
       (c$::asm-stmt->outputs asm-stmt)
       objs)
     (asm-input-list-peel (c$::asm-stmt->inputs asm-stmt)
                          objs)
     (c$::asm-stmt->clobbers asm-stmt)
     (c$::asm-stmt->labels asm-stmt))
    :measure (c$::asm-stmt-count asm-stmt))

  (define stmt-peel ((stmt stmtp)
                     (objs uid-ident-mapp))
    :returns (result stmtp)
    (stmt-case
     stmt
     :labeled
     (c$::stmt-labeled
       (label-peel (c$::stmt-labeled->label stmt)
                   objs)
       (stmt-peel (c$::stmt-labeled->stmt stmt)
                  objs))
     :compound
     (stmt-compound
       (comp-stmt-peel (stmt-compound->stmt stmt)
                       objs))
     :expr
     (stmt-expr
       (expr-option-peel (c$::stmt-expr->expr? stmt)
                         objs)
       (c$::stmt-expr->info stmt))
     :null-attrib
     (stmt-null-attrib (attrib-spec-peel
                         (c$::stmt-null-attrib->attrib stmt)
                         objs))
     :if (stmt-if (expr-peel (c$::stmt-if->test stmt)
                             objs)
                  (stmt-peel (c$::stmt-if->then stmt)
                             objs))
     :ifelse
     (stmt-ifelse (expr-peel (c$::stmt-ifelse->test stmt)
                             objs)
                  (stmt-peel (c$::stmt-ifelse->then stmt)
                             objs)
                  (stmt-peel (c$::stmt-ifelse->else stmt)
                             objs))
     :switch
     (c$::stmt-switch
       (expr-peel (c$::stmt-switch->target stmt)
                  objs)
       (stmt-peel (c$::stmt-switch->body stmt)
                  objs))
     :while
     (stmt-while (expr-peel (c$::stmt-while->test stmt)
                            objs)
                 (stmt-peel (c$::stmt-while->body stmt)
                            objs))
     :dowhile
     (stmt-dowhile
       (stmt-peel (c$::stmt-dowhile->body stmt)
                  objs)
       (expr-peel (c$::stmt-dowhile->test stmt)
                  objs))
     :for-expr
     (c$::stmt-for-expr
       (expr-option-peel (c$::stmt-for-expr->init stmt)
                         objs)
       (expr-option-peel (c$::stmt-for-expr->test stmt)
                         objs)
       (expr-option-peel (c$::stmt-for-expr->next stmt)
                         objs)
       (stmt-peel (c$::stmt-for-expr->body stmt)
                  objs))
     :for-declon
     (c$::stmt-for-declon
       (declon-peel (c$::stmt-for-declon->init stmt)
                    objs)
       (expr-option-peel (c$::stmt-for-declon->test stmt)
                         objs)
       (expr-option-peel (c$::stmt-for-declon->next stmt)
                         objs)
       (stmt-peel (c$::stmt-for-declon->body stmt)
                  objs))
     :goto (stmt-fix stmt)
     :gotoe
     (stmt-gotoe (expr-peel (c$::stmt-gotoe->label stmt)
                            objs))
     :continue (stmt-fix stmt)
     :break (stmt-fix stmt)
     :return
     (stmt-return
       (expr-option-peel (c$::stmt-return->expr? stmt)
                         objs)
       (c$::stmt-return->info stmt))
     :return-attrib
     (stmt-return-attrib
       (attrib-spec-peel
         (c$::stmt-return-attrib->attrib stmt)
         objs)
       (expr-peel (c$::stmt-return-attrib->expr stmt)
                  objs))
     :asm (c$::stmt-asm
            (asm-stmt-peel (c$::stmt-asm->stmt stmt)
                           objs))
     :for-ambig (stmt-fix stmt))
    :measure (stmt-count stmt))

  (define comp-stmt-peel ((comp-stmt comp-stmtp)
                          (objs uid-ident-mapp))
    :returns (result comp-stmtp)
    (comp-stmt
     (comp-stmt->labels comp-stmt)
     (block-item-list-peel (comp-stmt->items comp-stmt)
                           objs))
    :measure (comp-stmt-count comp-stmt))

  (define block-item-peel ((block-item block-itemp)
                           (objs uid-ident-mapp))
    :returns (result block-itemp)
    (block-item-case
     block-item
     :declon
     (block-item-declon (declon-peel
                          (c$::block-item-declon->declon block-item)
                          objs)
                        (c$::block-item-declon->info block-item))
     :stmt
     (block-item-stmt
       (stmt-peel (c$::block-item-stmt->stmt block-item)
                  objs)
       (c$::block-item-stmt->info block-item))
     :ambig (block-item-fix block-item))
    :measure (block-item-count block-item))

  (define block-item-list-peel
    ((block-item-list block-item-listp)
     (objs uid-ident-mapp))
    :returns (result block-item-listp)
    (if (endp block-item-list)
        nil
      (cons (block-item-peel (car block-item-list)
                             objs)
            (block-item-list-peel (cdr block-item-list)
                                  objs)))
    :measure (block-item-list-count block-item-list))

  :verify-guards :after-returns
  ;; :flag-local nil
  )
