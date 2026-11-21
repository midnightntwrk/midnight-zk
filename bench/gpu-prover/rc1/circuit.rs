use ff::Field;
use midnight_curves::Fq;
use midnight_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Constraints, Error, Expression, Instance,
        Selector,
    },
    poly::Rotation,
};

pub struct Chain {
    pub k: u32,
}

fn step(x: Fq) -> Fq {
    x.square() + Fq::from(3)
}

impl Chain {
    fn rows(&self) -> usize {
        (1 << self.k) - 16
    }

    pub fn instance(&self) -> [Fq; 2] {
        let start = Fq::from(7);
        [start, (0..4 * self.rows()).fold(start, |x, _| step(x))]
    }
}

#[derive(Clone)]
pub struct Config {
    advice: [Column<Advice>; 4],
    public: Column<Instance>,
    active: Selector,
}

impl Circuit<Fq> for Chain {
    type Config = Config;
    type FloorPlanner = SimpleFloorPlanner;
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self { k: self.k }
    }

    fn configure(meta: &mut ConstraintSystem<Fq>) -> Config {
        let advice = std::array::from_fn(|_| meta.advice_column());
        let public = meta.instance_column();
        let active = meta.selector();
        meta.enable_equality(advice[0]);
        meta.enable_equality(public);
        meta.create_gate("four squarings", |cells| {
            let mut chain = advice.map(|col| cells.query_advice(col, Rotation::cur())).to_vec();
            chain.push(cells.query_advice(advice[0], Rotation::next()));
            Constraints::with_selector(
                active,
                chain
                    .windows(2)
                    .map(|pair| {
                        pair[0].clone() * pair[0].clone() + Expression::Constant(Fq::from(3))
                            - pair[1].clone()
                    })
                    .collect(),
            )
        });
        Config {
            advice,
            public,
            active,
        }
    }

    fn synthesize(&self, config: Config, mut layouter: impl Layouter<Fq>) -> Result<(), Error> {
        let (start, end) = layouter.assign_region(
            || "chain",
            |mut region| {
                let mut x = Fq::from(7);
                let mut start = None;
                for row in 0..self.rows() {
                    config.active.enable(&mut region, row)?;
                    for col in config.advice {
                        let cell = region.assign_advice(|| "x", col, row, || Value::known(x))?;
                        if row == 0 && col == config.advice[0] {
                            start = Some(cell.cell());
                        }
                        x = step(x);
                    }
                }
                let end = region.assign_advice(
                    || "endpoint",
                    config.advice[0],
                    self.rows(),
                    || Value::known(x),
                )?;
                Ok((start.unwrap(), end.cell()))
            },
        )?;
        layouter.constrain_instance(start, config.public, 0)?;
        layouter.constrain_instance(end, config.public, 1)
    }
}
