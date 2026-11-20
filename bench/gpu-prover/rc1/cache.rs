use std::{
    env,
    fs::{self, File},
    io::{self, BufReader, BufWriter, Write},
    path::PathBuf,
};

use midnight_curves::Bls12;
use midnight_proofs::{
    plonk::{keygen_pk, keygen_vk_with_k},
    poly::kzg::params::ParamsKZG,
    utils::SerdeFormat,
};
use rand::{SeedableRng, rngs::StdRng};

use crate::{Chain, Key, Result};

pub fn dir(chain: &Chain) -> Result<PathBuf> {
    Ok(
        PathBuf::from(env::var_os("RC1_CACHE").ok_or("set RC1_CACHE")?)
            .join(format!("rc1-chain-v1-k{}", chain.k)),
    )
}

pub fn prepare(chain: &Chain) -> Result<()> {
    let dir = dir(chain)?;
    fs::create_dir_all(&dir)?;
    let lock = File::create(dir.join("prepare.lock"))?;
    lock.lock()?;
    let params_file = dir.join("params");
    let pk_file = dir.join("pk");
    if !params_file.exists() {
        let params = ParamsKZG::<Bls12>::unsafe_setup(chain.k, StdRng::seed_from_u64(0x524331));
        let tmp = dir.join("params.tmp");
        let mut writer = BufWriter::new(File::create(&tmp)?);
        params.write_custom(&mut writer, SerdeFormat::RawBytes)?;
        writer.flush()?;
        fs::rename(tmp, &params_file)?;
    }
    if !pk_file.exists() {
        let params = read_params(chain)?;
        let vk = keygen_vk_with_k::<_, crate::Scheme, _>(&params, chain, chain.k)?;
        let pk = keygen_pk(vk, chain)?;
        let tmp = dir.join("pk.tmp");
        let mut writer = BufWriter::new(File::create(&tmp)?);
        pk.write(&mut writer, SerdeFormat::RawBytes)?;
        writer.flush()?;
        fs::rename(tmp, pk_file)?;
    }
    Ok(())
}

fn read_params(chain: &Chain) -> Result<ParamsKZG<Bls12>> {
    let mut reader = BufReader::new(File::open(dir(chain)?.join("params"))?);
    let params = ParamsKZG::read_custom(&mut reader, SerdeFormat::RawBytes)?;
    if params.max_k() != chain.k {
        return Err(io::Error::other("cached SRS has wrong k").into());
    }
    Ok(params)
}

pub fn load(chain: &Chain) -> Result<(ParamsKZG<Bls12>, Key)> {
    let params = read_params(chain)?;
    let mut reader = BufReader::new(File::open(dir(chain)?.join("pk"))?);
    let pk = Key::read::<_, Chain>(&mut reader, SerdeFormat::RawBytes, ())?;
    if pk.get_vk().get_domain().k() != chain.k {
        return Err(io::Error::other("cached PK has wrong k").into());
    }
    Ok((params, pk))
}
