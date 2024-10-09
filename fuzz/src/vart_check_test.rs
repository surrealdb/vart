#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;
    use vart::{art::Tree, FixedSizeKey};

    #[derive(Debug)]
    enum TreeOperation {
        Get { key: u16 },
        Insert { key: u16, value: usize },
        Delete { key: u16 },
        RangeQuery { start: u16, end: u16 },
    }

    fn assert_tree_consistency(
        art_tree: &Tree<FixedSizeKey<16>, usize>,
        reference_map: &BTreeMap<u16, usize>,
        key: u16,
    ) {
        let art_key: FixedSizeKey<16> = FixedSizeKey::from(key);
        let expected_value = reference_map.get(&key).copied();
        let actual_value = art_tree.get(&art_key, 0).map(|(v, _, _)| v);

        assert_eq!(
            actual_value, expected_value,
            "Inconsistent values for key {}: ART {:?} != BTreeMap {:?}",
            key, actual_value, expected_value
        );
    }

    fn assert_range_query_consistency(
        art_tree: &Tree<FixedSizeKey<16>, usize>,
        reference_map: &BTreeMap<u16, usize>,
        start: u16,
        end: u16,
    ) {
        let expected_values: Vec<(FixedSizeKey<16>, usize)> = reference_map
            .range(start..=end)
            .map(|(&k, &v)| (FixedSizeKey::from(k), v))
            .collect();

        let start_key: FixedSizeKey<16> = start.into();
        let end_key: FixedSizeKey<16> = end.into();
        let actual_values: Vec<_> = art_tree
            .range(start_key..=end_key)
            .map(|(k, v, _, _)| (k.as_slice().into(), *v))
            .collect();

        assert_eq!(
            actual_values, expected_values,
            "Inconsistent range query results for range {}..={}: ART {:?} != BTreeMap {:?}",
            start, end, actual_values, expected_values
        );
    }

    #[test]
    fn test_tree_operations() {
        let mut art_tree = Tree::<FixedSizeKey<16>, usize>::new();
        let mut reference_map = BTreeMap::<u16, usize>::new();

        let operations = vec![
            TreeOperation::Insert { key: 1, value: 10 },
            TreeOperation::Insert { key: 2, value: 20 },
            TreeOperation::Get { key: 1 },
            TreeOperation::Delete { key: 1 },
            TreeOperation::Get { key: 1 },
            TreeOperation::RangeQuery { start: 1, end: 2 },
        ];

        for operation in operations {
            match operation {
                TreeOperation::Get { key } => {
                    assert_tree_consistency(&art_tree, &reference_map, key);
                }
                TreeOperation::Insert { key, value } => {
                    let art_key: FixedSizeKey<16> = FixedSizeKey::from(key);

                    reference_map.insert(key, value);
                    art_tree.insert(&art_key, value, 0, 0).expect("Insert failed");

                    assert_tree_consistency(&art_tree, &reference_map, key);
                }
                TreeOperation::Delete { key } => {
                    reference_map.remove(&key);
                    let art_key: FixedSizeKey<16> = FixedSizeKey::from(key);
                    art_tree.remove(&art_key);

                    assert_tree_consistency(&art_tree, &reference_map, key);
                }
                TreeOperation::RangeQuery { start, end } => {
                    assert_range_query_consistency(&art_tree, &reference_map, start, end);
                }
            }
        }

        for (key, expected_value) in reference_map.iter() {
            let art_key: FixedSizeKey<16> = FixedSizeKey::from(*key);
            let result = art_tree.get(&art_key, 0);
            if let Some((actual_value, _, _)) = result {
                assert_eq!(
                    Some(actual_value),
                    Some(*expected_value),
                    "Expected value for key {}: {:?} != {:?}, got {:?}",
                    key,
                    actual_value,
                    *expected_value,
                    result
                );
            } else {
                assert!(
                    result.is_none(),
                    "Expected None for key {}, got {:?}",
                    key,
                    result
                );
            }
        }
    }
}