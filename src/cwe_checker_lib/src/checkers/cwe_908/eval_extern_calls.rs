use std::collections::BTreeMap;

use serde_json::Value;

use crate::{
    abstract_domain::{DataDomain, RegisterDomain, SizedDomain},
    analysis::pointer_inference::ValueDomain,
};

use super::*;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, Hash, Clone)]
pub struct DataDomainSerial<T: RegisterDomain> {
    /// The byte size of the represented values.
    size: ByteSize,
    /// A map from base values to the corresponding offset.
    relative_values: BTreeMap<String, T>,
    /// An absolute value if the domain may represent an absolute value.
    absolute_value: Option<T>,
    /// An indicator whether the domain also represents values for which both the base and the offset are unknown.
    contains_top_values: bool,
}

impl<T: RegisterDomain> DataDomain<T> {
    pub fn into_datadomain_serial(&self) -> DataDomainSerial<T> {
        let rel = self
            .get_relative_values()
            .clone()
            .into_iter()
            .map(|(k, v)| (k.to_string(), v))
            .collect();
        DataDomainSerial {
            size: self.bytesize(),
            relative_values: rel,
            absolute_value: self.get_absolute_value().cloned(),
            contains_top_values: self.contains_top(),
        }
    }
}

pub fn eval_memset(tid: &Tid, parms: Vec<Option<DataDomain<ValueDomain>>>) {
    let mut serialized_parms = BTreeMap::new();
    serialized_parms.insert("memset", serde_json::to_value(tid).unwrap());
    for (i, parm) in parms.iter().enumerate() {
        if let Some(data_domain) = parm {
            let data_serial = data_domain.into_datadomain_serial();
            let data_serial_json = serde_json::to_value(data_serial).unwrap();

            match i {
                0 => serialized_parms.insert("target_pointer", data_serial_json),
                1 => serialized_parms.insert("constant", data_serial_json),
                2 => serialized_parms.insert("size_parameter", data_serial_json),
                _ => panic!("to many params"),
            };
        } else {
            match i {
                0 => serialized_parms
                    .insert("target_pointer", serde_json::to_value(Value::Null).unwrap()),
                1 => {
                    serialized_parms.insert("constant", serde_json::to_value(Value::Null).unwrap())
                }
                2 => serialized_parms
                    .insert("size_parameter", serde_json::to_value(Value::Null).unwrap()),
                _ => panic!("to many params"),
            };
        }
    }
    println!(
        "{},",
        serde_json::to_string_pretty(&serialized_parms).unwrap()
    );
}

pub fn eval_memcpy(tid: &Tid, parms: Vec<Option<DataDomain<ValueDomain>>>) {
    let mut serialized_parms = BTreeMap::new();
    serialized_parms.insert("memcpy", serde_json::to_value(tid).unwrap());
    for (i, parm) in parms.iter().enumerate() {
        if let Some(data_domain) = parm {
            let data_serial = data_domain.into_datadomain_serial();
            let data_serial_json = serde_json::to_value(data_serial).unwrap();

            match i {
                0 => serialized_parms.insert("target_pointer", data_serial_json),
                1 => serialized_parms.insert("source_pointer", data_serial_json),
                2 => serialized_parms.insert("size_parameter", data_serial_json),
                _ => panic!("to many params"),
            };
        } else {
            match i {
                0 => serialized_parms
                    .insert("target_pointer", serde_json::to_value(Value::Null).unwrap()),
                1 => serialized_parms
                    .insert("source_pointer", serde_json::to_value(Value::Null).unwrap()),
                2 => serialized_parms
                    .insert("size_parameter", serde_json::to_value(Value::Null).unwrap()),
                _ => panic!("to many params"),
            };
        }
    }
    println!(
        "{},",
        serde_json::to_string_pretty(&serialized_parms).unwrap()
    );
}

pub fn eval_free(tid: &Tid, parms: Vec<Option<DataDomain<ValueDomain>>>) {
    let mut serialized_parms = BTreeMap::new();
    serialized_parms.insert("free", serde_json::to_value(tid).unwrap());
    for (i, parm) in parms.iter().enumerate() {
        if let Some(data_domain) = parm {
            let data_serial = data_domain.into_datadomain_serial();
            let data_serial_json = serde_json::to_value(data_serial).unwrap();

            match i {
                0 => serialized_parms.insert("target_pointer", data_serial_json),
                _ => panic!("to many params"),
            };
        } else {
            match i {
                0 => serialized_parms
                    .insert("target_pointer", serde_json::to_value(Value::Null).unwrap()),
                _ => panic!("to many params"),
            };
        }
    }
    println!(
        "{},",
        serde_json::to_string_pretty(&serialized_parms).unwrap()
    );
}
