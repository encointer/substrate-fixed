// Copyright © 2018–2019 Trevor Spiteri

// This library is free software: you can redistribute it and/or
// modify it under the terms of either
//
//   * the Apache License, Version 2.0 or
//   * the MIT License
//
// at your option.
//
// You should have recieved copies of the Apache License and the MIT
// License along with the library. If not, see
// <https://www.apache.org/licenses/LICENSE-2.0> and
// <https://opensource.org/licenses/MIT>.

use core::fmt::{Formatter, Result as FmtResult};
use frac::{IsLessOrEqual, True, Unsigned, U128, U16, U32, U64, U8};
use serde::de::{self, Deserialize, Deserializer, MapAccess, SeqAccess, Visitor};
use serde::ser::{Serialize, SerializeStruct, Serializer};
use {
    FixedI128, FixedI16, FixedI32, FixedI64, FixedI8, FixedU128, FixedU16, FixedU32, FixedU64,
    FixedU8,
};

macro_rules! serde_fixed {
    ($Fixed:ident($NBits:ident) is $TBits:ident name $Name:expr) => {
        impl<Frac> Serialize for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: Serializer,
            {
                let bits = self.to_bits();
                let mut state = serializer.serialize_struct($Name, 1)?;
                state.serialize_field("bits", &bits)?;
                state.end()
            }
        }

        impl<'de, Frac> Deserialize<'de> for $Fixed<Frac>
        where
            Frac: Unsigned + IsLessOrEqual<$NBits, Output = True>,
        {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: Deserializer<'de>,
            {
                struct FixedVisitor;

                impl<'de> Visitor<'de> for FixedVisitor {
                    type Value = $TBits;

                    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
                        formatter.write_str("struct ")?;
                        formatter.write_str($Name)
                    }

                    fn visit_seq<V>(self, mut seq: V) -> Result<$TBits, V::Error>
                    where
                        V: SeqAccess<'de>,
                    {
                        let bits = seq
                            .next_element()?
                            .ok_or_else(|| de::Error::invalid_length(0, &self))?;
                        Ok(bits)
                    }

                    fn visit_map<V>(self, mut map: V) -> Result<$TBits, V::Error>
                    where
                        V: MapAccess<'de>,
                    {
                        let mut bits = None;
                        while let Some(key) = map.next_key()? {
                            match key {
                                Field::Bits => {
                                    if bits.is_some() {
                                        return Err(de::Error::duplicate_field("bits"));
                                    }
                                    bits = Some(map.next_value()?);
                                }
                            }
                        }
                        let bits = bits.ok_or_else(|| de::Error::missing_field("bits"))?;
                        Ok(bits)
                    }
                }

                let bits = deserializer.deserialize_struct($Name, FIELDS, FixedVisitor)?;
                Ok($Fixed::from_bits(bits))
            }
        }
    };
}

serde_fixed! { FixedI8(U8) is i8 name "FixedI8<_>" }
serde_fixed! { FixedI16(U16) is i16 name "FixedI16<_>" }
serde_fixed! { FixedI32(U32) is i32 name "FixedI32<_>" }
serde_fixed! { FixedI64(U64) is i64 name "FixedI64<_>" }
serde_fixed! { FixedI128(U128) is i128 name "FixedI128<_>" }
serde_fixed! { FixedU8(U8) is u8 name "FixedU8<_>" }
serde_fixed! { FixedU16(U16) is u16 name "FixedU16<_>" }
serde_fixed! { FixedU32(U32) is u32 name "FixedU32<_>" }
serde_fixed! { FixedU64(U64) is u64 name "FixedU64<_>" }
serde_fixed! { FixedU128(U128) is u128 name "FixedU128<_>" }

const FIELDS: &'static [&'static str] = &["bits"];

enum Field {
    Bits,
}

impl<'de> Deserialize<'de> for Field {
    fn deserialize<D>(deserializer: D) -> Result<Field, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct FieldVisitor;

        impl<'de> Visitor<'de> for FieldVisitor {
            type Value = Field;

            fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
                formatter.write_str("`bits`")
            }

            fn visit_str<E>(self, value: &str) -> Result<Field, E>
            where
                E: de::Error,
            {
                match value {
                    "bits" => Ok(Field::Bits),
                    _ => Err(de::Error::unknown_field(value, FIELDS)),
                }
            }
        }

        deserializer.deserialize_identifier(FieldVisitor)
    }
}
