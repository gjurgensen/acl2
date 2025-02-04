; A utility to get the user's username
;
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "read-acl2-oracle"))
(local (include-book "update-acl2-oracle"))

(local (in-theory (disable state-p1 update-acl2-oracle read-acl2-oracle w)))

(defttag get-username) ; due to the sys-call+

(defun strip-last-char (string)
  (declare (xargs :guard (stringp string)))
  (coerce (butlast (coerce string 'list) 1) 'string))

;; Returns (mv username state)
;; Could move this to a separate book...
(defund get-username (state)
  (declare (xargs :stobjs state))
  (b* (((mv erp username-and-newline state)
        (sys-call+ "whoami" '() state))
       ((when erp)
        (er hard? 'get-username "Failed to get username.")
        (mv "BAD-USERNAME" state))
       ((when (not (stringp username-and-newline)))
        (mv "BAD-USERNAME" state))
       ;; Strip the final newline:
       (username (strip-last-char username-and-newline)))
    (mv username state)))

(defthm stringp-of-mv-nth-0-of-get-username
  (stringp (mv-nth 0 (get-username state)))
  :hints (("Goal" :in-theory (enable get-username))))

(defthm state-p1-of-mv-nth-1-of-get-username
  (implies (and (symbolp name)
                (state-p1 state))
           (state-p1 (mv-nth 1 (get-username state))))
  :hints (("Goal" :in-theory (enable get-username))))

(defthm w-of-mv-nth-1-of-get-username
  (equal (w (mv-nth 1 (get-username state)))
         (w state))
  :hints (("Goal" :in-theory (e/d (get-username) (put-global)))))
