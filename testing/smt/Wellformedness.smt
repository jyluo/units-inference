(declare-fun |5-s| () Int)
(declare-fun |5-rad| () Int)
(declare-fun |5-m| () Int)
(declare-fun |5-deg| () Int)
(declare-fun |5-PREFIX| () Int)
(declare-fun |5-BOT| () Bool)
(declare-fun |5-TOP| () Bool)

; Paste slot wellformedness encoding for slot 5 here
(assert (let ((a!1 (and |5-TOP|
                (= |5-PREFIX| 0)
                (= |5-deg| 0)
                (= |5-m| 0)
                (= |5-rad| 0)
                (= |5-s| 0)))
      (a!2 (and |5-BOT|
                (= |5-PREFIX| 0)
                (= |5-deg| 0)
                (= |5-m| 0)
                (= |5-rad| 0)
                (= |5-s| 0))))
(let ((a!3 (or (not (and (not |5-TOP|) (not |5-BOT|))) (not a!1)))
      (a!4 (or (not (and (not |5-TOP|) (not |5-BOT|))) (not a!2))))
  (and (or (and (not |5-TOP|) (not |5-BOT|)) a!1 a!2)
       a!3
       a!4
       (or (not a!1) (not a!2))))))

; without constraints on top, bot, or prefixes, it should be sat
(check-sat)
; (get-model)

; with only top = true, it should be sat
(push)
(assert |5-TOP|)
(check-sat)
; (get-model)
(pop)

; with top = true & bot = false, it should be sat
(push)
(assert |5-TOP|)
(assert (not |5-BOT|))
(check-sat)
; (get-model)
(pop)

; with only bot = true, it should be sat
(push)
(assert |5-BOT|)
(check-sat)
; (get-model)
(pop)

; with top = false & bot = true, it should be sat
(push)
(assert (not |5-TOP|))
(assert |5-BOT|)
(check-sat)
; (get-model)
(pop)

; with top = bot = false, it should be sat
(push)
(assert (not |5-TOP|))
(assert (not |5-BOT|))
(check-sat)
; (get-model)
(pop)

; with top = bot = true, it should be unsat
(push)
(assert |5-TOP|)
(assert |5-BOT|)
(check-sat)
(pop)
