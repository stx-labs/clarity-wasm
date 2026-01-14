use clar2wasm::tools::evaluate;

mod tests {
    /// This files purpose is to add examples of generated values that failed,
    /// so that we can be sure they won't fail again after some random refactor
    /// in the future.
    use clar2wasm::tools::{crosscheck, crosscheck_compare_only, evaluate};
    use clarity::vm::types::{ListData, ListTypeData, ResponseData, SequenceData, TypeSignature};
    use clarity::vm::Value;

    use crate::PropValue;

    fn evaluate_expression(expr: &str) {
        let v: PropValue = evaluate(expr)
            .unwrap()
            .expect("Failed to evaluate expression")
            .into();
        assert_eq!(expr, v.to_string());
    }

    #[test]
    fn list_ok_response() {
        evaluate_expression(
            r#"(list (ok (ok -1475)) (ok (err u115911259112154807243168097824046874107)))"#,
        )
    }

    #[test]
    fn list_err_response() {
        evaluate_expression(
            r#"(list (err (ok -1475)) (err (err u115911259112154807243168097824046874107)))"#,
        )
    }

    #[test]
    fn list_some_response() {
        evaluate_expression(
            r#"(list (some (ok -1475)) (some (err u115911259112154807243168097824046874107)))"#,
        )
    }

    #[test]
    fn is_eq_list_opt_resp() {
        let l = "(list none (some (ok 1)))";
        crosscheck(&format!(r#"(is-eq {l} {l})"#), Ok(Some(Value::Bool(true))));
    }

    #[test]
    fn default_to() {
        crosscheck(
            "(default-to (list 100) (some (list 1 2 3)))",
            Ok(Some(Value::Sequence(SequenceData::List(ListData {
                data: vec![Value::Int(1), Value::Int(2), Value::Int(3)],
                type_signature: ListTypeData::new_list(TypeSignature::IntType, 3).unwrap(),
            })))),
        );
    }

    #[test]
    fn default_to_2() {
        crosscheck(
        "(default-to (err -8865319038999812741356205373046857778) (some (ok 94740629357611018681632671610045749418)))",
        Ok(Some(Value::Response(ResponseData{
            committed: true,
            data: Box::new(Value::Int(94740629357611018681632671610045749418))
        })))
    );
    }

    #[test]
    fn filter_regression() {
        let snippet = r#"
    (define-private (foo
        (el (tuple (NBlr (optional (string-utf8 24))) (PXjxHEkOFOT (string-ascii 21)) (TzZsYKMTEbprp (string-utf8 30)) (j (tuple (DjhalL (string-utf8 8)) (NOEuhh uint) (dBJLekcnsjHwdB uint) (jiZqxSxeVBsYtn principal) (oPLU (string-ascii 71)) (sSddAEMlw (buff 12)))) (nUR uint) (nniRNfmDI (list 31 bool))))) (is-eq el (tuple (NBlr none) (PXjxHEkOFOT "b,rCCv^\"O.EZfvpQ1bO?@") (TzZsYKMTEbprp u"``..\u{9FCD7}\u{108D35}\u{7046F}\u{E7660}\u{FFFD}\u{FFFD}\u{FD}\u{468}\"\u{FE}$\u{5D6DB}\u{D0E1C}\u{EE7AC}\u{1F574}\u{FFFD}?\u{C544}<=\u{85FF5}.\u{D67B8}d\u{202E}'") (j (tuple (DjhalL u"`\u{23A}\\\u{2A5E1}?\u{B}\u{5C142}\u{10F05B}") (NOEuhh u137436105837418320392895712035305059757) (dBJLekcnsjHwdB u86607750441816061623548602539664746924) (jiZqxSxeVBsYtn 'SP2CJH9CK2GJW5E06AA9MMVJMP310RV1APPKXEWVV) (oPLU "iyaO4 Co(Y#Ub&qy-n2i^s^k.E^r7BO}RV18vDhi2kek!)s:nRCq5@I4dE'z]\"9&49JW^P^") (sSddAEMlw 0xd2d89062eb20c15f49939349))) (nUR u156826313668429625148491396170213373157) (nniRNfmDI (list false false true false false false false true true false true false true true false false true false true))))
    )

        (filter foo (list (tuple (NBlr none) (PXjxHEkOFOT "b,rCCv^\"O.EZfvpQ1bO?@") (TzZsYKMTEbprp u"``..\u{9FCD7}\u{108D35}\u{7046F}\u{E7660}\u{FFFD}\u{FFFD}\u{FD}\u{468}\"\u{FE}$\u{5D6DB}\u{D0E1C}\u{EE7AC}\u{1F574}\u{FFFD}?\u{C544}<=\u{85FF5}.\u{D67B8}d\u{202E}'") (j (tuple (DjhalL u"`\u{23A}\\\u{2A5E1}?\u{B}\u{5C142}\u{10F05B}") (NOEuhh u137436105837418320392895712035305059757) (dBJLekcnsjHwdB u86607750441816061623548602539664746924) (jiZqxSxeVBsYtn 'SP2CJH9CK2GJW5E06AA9MMVJMP310RV1APPKXEWVV) (oPLU "iyaO4 Co(Y#Ub&qy-n2i^s^k.E^r7BO}RV18vDhi2kek!)s:nRCq5@I4dE'z]\"9&49JW^P^") (sSddAEMlw 0xd2d89062eb20c15f49939349))) (nUR u156826313668429625148491396170213373157) (nniRNfmDI (list false false true false false false false true true false true false true true false false true false true)))))"#;

        crosscheck_compare_only(snippet);
    }

    #[test]
    fn filter_regression_ro() {
        let snippet = r#"
    (define-read-only (foo
        (el (tuple (NBlr (optional (string-utf8 24))) (PXjxHEkOFOT (string-ascii 21)) (TzZsYKMTEbprp (string-utf8 30)) (j (tuple (DjhalL (string-utf8 8)) (NOEuhh uint) (dBJLekcnsjHwdB uint) (jiZqxSxeVBsYtn principal) (oPLU (string-ascii 71)) (sSddAEMlw (buff 12)))) (nUR uint) (nniRNfmDI (list 31 bool))))) (is-eq el (tuple (NBlr none) (PXjxHEkOFOT "b,rCCv^\"O.EZfvpQ1bO?@") (TzZsYKMTEbprp u"``..\u{9FCD7}\u{108D35}\u{7046F}\u{E7660}\u{FFFD}\u{FFFD}\u{FD}\u{468}\"\u{FE}$\u{5D6DB}\u{D0E1C}\u{EE7AC}\u{1F574}\u{FFFD}?\u{C544}<=\u{85FF5}.\u{D67B8}d\u{202E}'") (j (tuple (DjhalL u"`\u{23A}\\\u{2A5E1}?\u{B}\u{5C142}\u{10F05B}") (NOEuhh u137436105837418320392895712035305059757) (dBJLekcnsjHwdB u86607750441816061623548602539664746924) (jiZqxSxeVBsYtn 'SP2CJH9CK2GJW5E06AA9MMVJMP310RV1APPKXEWVV) (oPLU "iyaO4 Co(Y#Ub&qy-n2i^s^k.E^r7BO}RV18vDhi2kek!)s:nRCq5@I4dE'z]\"9&49JW^P^") (sSddAEMlw 0xd2d89062eb20c15f49939349))) (nUR u156826313668429625148491396170213373157) (nniRNfmDI (list false false true false false false false true true false true false true true false false true false true))))
    )

        (filter foo (list (tuple (NBlr none) (PXjxHEkOFOT "b,rCCv^\"O.EZfvpQ1bO?@") (TzZsYKMTEbprp u"``..\u{9FCD7}\u{108D35}\u{7046F}\u{E7660}\u{FFFD}\u{FFFD}\u{FD}\u{468}\"\u{FE}$\u{5D6DB}\u{D0E1C}\u{EE7AC}\u{1F574}\u{FFFD}?\u{C544}<=\u{85FF5}.\u{D67B8}d\u{202E}'") (j (tuple (DjhalL u"`\u{23A}\\\u{2A5E1}?\u{B}\u{5C142}\u{10F05B}") (NOEuhh u137436105837418320392895712035305059757) (dBJLekcnsjHwdB u86607750441816061623548602539664746924) (jiZqxSxeVBsYtn 'SP2CJH9CK2GJW5E06AA9MMVJMP310RV1APPKXEWVV) (oPLU "iyaO4 Co(Y#Ub&qy-n2i^s^k.E^r7BO}RV18vDhi2kek!)s:nRCq5@I4dE'z]\"9&49JW^P^") (sSddAEMlw 0xd2d89062eb20c15f49939349))) (nUR u156826313668429625148491396170213373157) (nniRNfmDI (list false false true false false false false true true false true false true true false false true false true)))))"#;

        crosscheck_compare_only(snippet);
    }

    #[test]
    fn filter_result_private() {
        let snippet = "
(define-private (is-even? (x int))
        (is-eq (* (/ x 2) 2) x))

(define-private (grob (x (response int int)))
  (match x
    a (is-even? a)
    b (not (is-even? b))))

(filter grob (list (ok 1) (err 1)))";

        crosscheck(snippet, evaluate("(list (err 1))"));
    }

    #[test]
    fn filter_result_read_only() {
        let snippet = "
(define-read-only (is-even? (x int))
        (is-eq (* (/ x 2) 2) x))

(define-private (grob (x (response int int)))
  (match x
    a (is-even? a)
    b (not (is-even? b))))

(filter grob (list (err 1) (err 1)))";

        crosscheck(snippet, evaluate("(list (err 1) (err 1))"));
    }

    //
    // Module with tests that should only be executed
    // when running Clarity::V2 or Clarity::v3.
    //
    #[cfg(not(feature = "test-clarity-v1"))]
    #[cfg(test)]
    mod clarity_v2_v3 {
        use super::*;

        #[test]
        fn to_consensus_buff_1() {
            use hex::FromHex as _;

            crosscheck(
                "(to-consensus-buff? (err {a: 1}))",
                Ok(Some(
                    Value::some(
                        Value::buff_from(
                            Vec::from_hex("080c0000000101610000000000000000000000000000000001")
                                .unwrap(),
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                )),
            );
        }
    }
}

#[test]
fn foo() {
    let snippet = std::fs::read_to_string("../try.clar").unwrap();
    evaluate(&snippet).expect("Fail");
    //interpret(&snippet).expect("Fail");
}
