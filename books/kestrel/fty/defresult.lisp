; FTY Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/defflatsum" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc defresult

  :parents (fty-extensions fty)

  :short "Introduce a fixtype for good results and error results."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-intro

    (xdoc::p
     "This is an experimental tool for now.")

    (xdoc::p
     "It is common for a function to return an error result in certain cases.
      Otherwise, the function returns a good (i.e. non-error) result.")

    (xdoc::p
     "In ACL2, an approach is to have the function return multiple results:
      an error result
      (which is @('nil') if there is no error),
      and a good result
      (which is irrelevant if the error result is non-@('nil'));
      for instance, this is the idiom of "
     (xdoc::seetopic "acl2::error-triple" "error triples")
     ". Another approach is to have the function return
      either an error result or a good result,
      which requires error and good results to be disjoint.")

    (xdoc::p
     "The two approaches have relative advantages and disadvantages.
      An advantage of the first approach is that
      disjointness of error and good results is not required
      and that each result has always the same type.
      However, a disadvantage is that
      even though the good result is irrelevant
      when the error result is non-@('nil'),
      some good result must be nonetheless returned,
      which might be accidentally used, as nothing could prevent that.
      Returning something like @('nil') as good result means that,
      unless @('nil') happens to be a good result,
      it is not the case that the good result
      always has the type of good results,
      leading to conditional return type theorems
      instead of unconditional ones;
      the latter are more efficient, and conceptually cleaner,
      but there is nothing technically wrong with conditional ones either.
      The second approach avoids this issue,
      because if there is an error result then there is no good result at all;
      the downside is that the result may have two different types.
      Since disjunctions are awkward in rewrite rules,
      it is beneficial to always introduce a type for
      the union of good and error results,
      and use that as the return type of the function.
      But then one needs rules to handle the inherent disjunction.")

    (xdoc::p
     "When functions naturally return multiple results (via @(tsee mv)),
      the first approach adds an error result,
      while the second approach could be applied to one of the results
      (e.g. the ``main'' one, if there is such a thing).
      Better yet from a conceptual point of view,
      the function can be made to return a single result,
      instead of multiple ones,
      that is either an error or a tuple of the good results.
      This is less efficient than multiple results
      (efficiency is indeed the purpose of multiple results with @(tsee mv)),
      but it may be more appropriate for a higher-level specification function,
      where issues of efficiency should be secondary,
      and where it may be more important that, in case of error,
      no dummy results are returned, so they cannot be accidentally used.
      The term `tuple' above is used in a broad sense:
      it does not have to be a list of values;
      it could be a value of a @(tsee fty::defprod) type, for example.
      The claim above that
      issues of efficiency should be secondary in specification functions
      fits into a vision in which tools like "
     (xdoc::seetopic "apt::apt" "APT")
     " are used to turn possibly inefficient or even non-executable functions
      into efficient ones.
      When instead, for expediency or practicality, a compromise is sought
      in which the same function is used for specification and execution
      (which sometimes also involves uses of @(tsee mbe)),
      then other considerations may apply,
      and the first approach above may be preferable to the second one.
      Nonetheless, there are applications where the second approach fits well.")

    (xdoc::p
     "When calling functions that may return error results
      (whether the first or second approach above is used),
      it is common to check whether the returned result is an error one,
      and in that case also return an error,
      otherwise continuing the computation if the returned result is a good one.
      When using the error triple idiom,
      ACL2 provides @(tsee er-let*) to handle this pattern,
      which propagates the error triples unchanged;
      @(tsee b*) provides the "
     (xdoc::seetopic "acl2::patbind-er" "@('er') binder")
     ", which expands into something like @(tsee er-let*).")

    (xdoc::p
     "The @('defresult') macro provides support for the second approach above.
      Given a fixtype of good results,
      it introduces a fixtype of good and error results,
      where the fixtype of error results is @(tsee reserr)
      (from the first three letters of each of the two words of `result error'),
      which is provided along with @('defresult').
      This macro also generates rules
      to reason about the disjunction of good and error results.
      To return an error (when an error condition arises),
      the constructor @('reserr') of the @(tsee reserr) fixtype can be used:
      it takes an argument of any type.
      Along with @('defresult'),
      a @(tsee b*) binder @(tsee patbind-ok) is provided
      to support the check-and-propagate-error pattern described above.")

    (xdoc::p
     "When using @(tsee define),
      which provides automatic binding of @('__function__')
      to the current function symbol,
      it may be useful to automatically incorporate this information
      into the error result.
      To this end, a macro @(tsee reserrf) is provided
      that automatically adds the function information
      to the information passed explicitly as input to the macro.
      A macro @(tsee reserrf-push) is also provided
      to add function and other information
      to an error of the form
      returned by @(tsee reserrf) or @(tsee reserrf-push),
      resulting in a stack of error information
      corresponding to the call stack.
      The @(tsee patbind-okf) binder automates the check-and-propagation
      of errors that include function information.")

    (xdoc::p
     "The @(tsee reserrf) and @(tsee reserrf-push) macros,
      and the @(tsee patbind-okf) binder,
      may be very useful for debugging,
      or in general to provide informative error information.
      They may be less useful for higher-level specifications,
      in which errors do not carry much information
      (as producing and consuming that information
      may detract from the clarity and conciseness of the specification):
      for higher-level specifications,
      the simpler function @(tsee reserr) and binder @(tsee patbind-ok)
      may be more appropriate.
      Note that the @('f') in the names of the first set of items conveys
      that they are a version of the simpler ones
      that take the function name bound to @('__function__') into account;
      note also that there is no @('reserr-push'),
      since it is not needed for
      the simpler errors and checks and propagation.
      We also remark that the simpler ones can be used
      in code not written using @(tsee define).")

    (xdoc::p
     "The fact that the same error result type, namely @(tsee reserr),
      is used in all the result types introduced by @('defresult')
      is crucial to supporting the kind of error propagation explained above:
      the same type of error result may be returned
      by any function that returns a type defined via @('defresult'),
      even if the good result types are different.
      It is also crucial that the result type is defined
      as a flat, and not tagged, union of good and error results:
      otherwise, error results would have to be unwrapped and wrapped
      depending on the result types of the callee and caller,
      using different unwrapping and wrapping function for each type.")

    (xdoc::p
     "The fixtype of good and error results introduced by @('defresult')
      is similar to an instance of Rust's polymorphic type @('Result'),
      from which the `result' part of @('defresult') is taken.
      However, while the Rust type is parameterized over
      both the good and error result types,
      in @('defresult') errors always have the same type.
      Nonetheless, @(tsee reserr) is defined to
      allow any ACL2 value to be contained in an error result,
      so the lack of parameterization over the type of errors
      does not limit expressivity."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-form

    (xdoc::codeblock
     "(defresult type"
     "           :ok ..."
     "           :pred ..."
     "           :fix ..."
     "           :equiv ..."
     "           :parents ..."
     "           :short ..."
     "           :long ..."
     "           :prepwork ..."
     "  )"))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-inputs

    (xdoc::desc
     "@(':type')"
     (xdoc::p
      "A symbol that specifies the name of the new fixtype."))

    (xdoc::desc
     "@(':ok')"
     (xdoc::p
      "A symbol that specifies the fixtype of the good results.
       Let @('ok') be the recognizer of this fixtype."))

    (xdoc::desc
     "@(':pred')"
     (xdoc::p
      "A symbol that specifies the name of the fixtype's recognizer.
       If this is @('nil') (the default),
       the name of the recognizer is @('type') followed by @('-p')."))

    (xdoc::desc
     "@(':fix')"
     (xdoc::p
      "A symbol that specifies the name of the fixtype's fixer.
       If this is @('nil') (the default),
       the name of the fixer is @('type') followed by @('-fix')."))

    (xdoc::desc
     "@(':equiv')"
     (xdoc::p
      "A symbol that specifies the name of the fixtype's equivalence.
       If this is @('nil') (the default),
       the name of the equivalence is @('type') followed by @('-equiv')."))

    (xdoc::desc
     (list
      "@(':parents')"
      "@(':short')"
      "@(':long')")
     (xdoc::p
      "These, if present, are added to
       the XDOC topic generated for the fixtype."))

    (xdoc::desc
     "@(':prepwork')"
     (xdoc::p
      "A list of preparatory event forms.
       See the `" xdoc::*evmac-section-generated-title* "' section.")))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-appconds

    defresult

    (xdoc::p
     "The fixtype specified by @(':ok')
      must be disjoint from @(tsee reserr).
      Currently this is not quite explicated
      as an applicability condition as in other event macros,
      but the macro will fail if the disjointness cannot be proved.
      The @(':prepwork') option may be used to add events
      to help the proofs (e.g. lemmas and rule enablements);
      these events should be normally made local."))

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

   (xdoc::evmac-section-generated

    (xdoc::desc
     "@('type')"
     (xdoc::p
      "The fixtype of good and error results."))

    (xdoc::desc
     "@('pred')"
     (xdoc::p
      "The recognizer for the fixtype @('type')."))

    (xdoc::desc
     "@('fix')"
     (xdoc::p
      "The fixer for the fixtype @('type')."))

    (xdoc::desc
     "@('equiv')"
     (xdoc::p
      "The equivalence for the fixtype @('type')."))

    (xdoc::desc
     "@('pred-when-ok')"
     (xdoc::p
      "A theorem asserting that
       a value in the fixtype specified by @(':ok')
       is also in the fixtype @('type'):")
     (xdoc::codeblock
      "(implies (ok x)"
      "         (pred x))"))

    (xdoc::desc
     "@('pred-when-reserrp')"
     (xdoc::p
      "A theorem asserting that
       a value in the fixtype @(tsee reserrp)
       is also in the fixtype @('type'):")
     (xdoc::codeblock
      "(implies (reserrp x)"
      "         (pred x))"))

    (xdoc::desc
     "@('ok-when-pred-and-not-error')"
     (xdoc::p
      "A theorem asserting that
       a value in the fixtype @('type')
       that is not in the fixtype @('reserr')
       is in the fixtype specified by @(':ok'):")
     (xdoc::codeblock
      "(implies (and (pred x)"
      "              (not (reserrp x)))"
      "         (ok x))")
     (xdoc::p
      "This theorem is disabled by default,
       because it backchains from @('ok') to @('pred'),
       where the former may be used without any reference to the latter."))

    (xdoc::p
     "The above events are preceded by
      the events specified in @(':prepwork'), if any.")

    (xdoc::p
     "Currently the fixtype @('type') and the first two theorems above
      are generated via @(tsee defflatsum),
      but this may change in the future.
      Users should not rely on the generation of @(tsee defflatsum),
      but just on the generation of the items described above."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defprod reserr
  :parents (defresult)
  :short "Fixtype of error results."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the fixtype of error results for @(tsee defresult);
     see the introduction of @(tsee defresult) for background and motivation.")
   (xdoc::p
    "An error result consists of some unconstrained information,
     wrapped with @(':error') to make it distinct from any good value
     (assuming that good values do not have the form @('(:error ...)'),
     a condition that seems reasonably easy to satisfy)."))
  ((info acl2::any))
  :tag :error
  :pred reserrp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defoption reserr-option
  reserr
  :parents (defresult)
  :short "Fixtype of optional error results."
  :long
  (xdoc::topstring
   (xdoc::p
    "This can be used for results that
     either are errors or carry no information otherwise.
     That is, @('nil') is the (only) good result."))
  :pred reserr-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defmacro+
 reserrf (info)
 :parents (defresult)
 :short "Return an error result with a singleton stack."
 :long
 (xdoc::topstring
  (xdoc::p
   "This macro constructs an error result of fixtype @(tsee reserr)
    with the specified information @('info'),
    accompanied by the name of the current function @('fn'),
    as a doublet @('(fn info)').
    A singleton list with this doublet is returned.
    This is a singleton stack, in the sense explained in @(tsee defresult).")
  (xdoc::p
   "This assumes that @('__function__') is bound to the function name,
    which happens automatically with @(tsee define).")
  (xdoc::p
   "This macro is a bit like the @('reserr') constructor
    of the fixtype @(tsee reserr),
    but the @('f') in the name conveys that
    it adds the name of the function to the infomation passed as argument."))
 `(make-reserr :info (list (list __function__ ,info))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defmacro+
 reserrf-push (error &optional info)
 :parents (defresult)
 :short "Push the current function onto the stack of an error result,
         optionally with additional information."
 :long
 (xdoc::topstring
  (xdoc::p
   "This is useful when receiving an error result from a called function,
    to add the caller to the stack, and possibly more information,
    before propagating the error.
    This addition is handled automatically when using @(tsee patbind-okf),
    actually using @('nil') as extra information;
    when that binder cannot be used for some reason,
    or when additional information must be pushed,
    then this @('reserrf-push') macro may come handy.")
  (xdoc::p
   "This assumes that @('__function__') is bound to the current function name,
    which is automatically the case when using @(tsee define)."))
 `(b* ((stack (reserr->info ,error)))
    (reserr (cons (list __function__ ,info) stack))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-b*-binder ok
  :parents (defresult)
  :short "@(tsee b*) binder for checking and propagating
          error results of the fixtype @(tsee reserr)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is somewhat similar to @(tsee acl2::patbind-er),
     but it is for " (xdoc::seetopic "defresult" "result types") ".")
   (xdoc::p
    "It checks whether the value of the bound term is an error,
     returning the same error if the check succeeds.
     Otherwise, the binder proceeds with the rest of the computation.")
   (xdoc::p
    "This binder is used as follows:")
   (xdoc::codeblock
    "(b* (..."
    "     ((ok <pattern>) <term>)"
    "     ...)"
    "  ...)")
   (xdoc::p
    "Note that the argument of @('(ok ...)')
     may be a supported single-valued @(tsee b*) pattern,
     e.g. @('(ok (cons x y))').")
   (xdoc::p
    "In order to support such a pattern,
     we generate an initial binding to a variable,
     a test of whether it is an error or not,
     and then a second binding of the pattern to the variable if not.
     As done in other binders that come with @(tsee b*),
     we pick a name for the first variable
     that is unlikely to occur in code."))
  :decls
  ((declare (xargs :guard (acl2::destructure-guard ok args acl2::forms 1))))
  :body
  `(b* ((patbinder-ok-fresh-variable-for-result ,(car acl2::forms))
        ((when (reserrp patbinder-ok-fresh-variable-for-result))
         (reserrf-push patbinder-ok-fresh-variable-for-result))
        (,(car args) patbinder-ok-fresh-variable-for-result))
     ,acl2::rest-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-b*-binder okf
  :parents (defresult)
  :short "@(tsee b*) binder for checking and propagating
          error results of the fixtype @(tsee reserr)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee patbind-ok),
     but it takes into account the current function name,
     assuming that @('__funtion__') is bound to it
     (which is automatically the case when using @(tsee define)).
     This binder checks whether the value of the bound term is an error,
     returning a slightly modified error if the check succeeds.
     Otherwise, the binder proceeds with the rest of the computation."))
  :decls
  ((declare (xargs :guard (acl2::destructure-guard okf args acl2::forms 1))))
  :body
  `(b* ((patbinder-okf-fresh-variable-for-result ,(car acl2::forms))
        ((when (reserrp patbinder-okf-fresh-variable-for-result))
         (reserrf-push patbinder-okf-fresh-variable-for-result))
        (,(car args) patbinder-okf-fresh-variable-for-result))
     ,acl2::rest-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defresult-macro-definition
  :parents (defresult)
  :short "Definition of @(tsee defresult)."
  :long (xdoc::topstring-@def "defresult")

  (defmacro defresult (type
                       &key
                       ok
                       pred
                       fix
                       equiv
                       (parents 'nil parents?)
                       short
                       long
                       prepwork)
    `(make-event (defresult-fn
                   ',type
                   ',ok
                   ',pred
                   ',fix
                   ',equiv
                   ',parents
                   ',parents?
                   ',short
                   ',long
                   ',prepwork
                   (w state))))

  (define defresult-fn (type
                        ok
                        pred
                        fix
                        equiv
                        parents
                        parents?
                        short
                        long
                        prepwork
                        (wrld plist-worldp))
    :returns event ; PSEUDO-EVENT-FORMP
    :mode :program
    (b* ((fty-table (get-fixtypes-alist wrld))
         (fty-info (find-fixtype ok fty-table))
         (ok-pred (fixtype->pred fty-info))
         (type-pred (or pred (add-suffix type "-P")))
         (type-fix (or fix (add-suffix type "-FIX")))
         (type-equiv (or equiv (add-suffix type "-EQUIV")))
         (ok-pred-when-type-pred-and-not-reserr
          (acl2::packn-pos (list ok-pred '-when- type-pred '-and-not-reserrp)
                           type)))
      `(encapsulate ()
         ,@prepwork
         (defflatsum ,type
           ,@(and parents? (list :parents parents))
           ,@(and short (list :short short))
           ,@(and long (list :long long))
           (:ok ,ok)
           (:err reserr)
           :pred ,type-pred
           :fix ,type-fix
           :equiv ,type-equiv)
         (defruled ,ok-pred-when-type-pred-and-not-reserr
           (implies (and (,type-pred x)
                         (not (reserrp x)))
                    (,ok-pred x))
           :enable ,type-pred)))))
