# Google Cloud workers for the Friedmann missions

VM creation is blocked in this session: `gcloud` cannot resolve `compute.googleapis.com`. No create request was sent and no VM was observed or claimed to exist. The project was read from the existing local Google Cloud configuration.

The prepared setup uses two `e2-standard-4` instances, each with 4 vCPUs, 16 GB RAM, a 60 GB balanced boot disk and Ubuntu 24.04 LTS, in `europe-west3-a`. Startup installs Lean 4.33.1 and downloads the exact Mathlib revision used by the mission packages. The VMs have no attached service account. They stop after 24 hours; their boot disks remain until explicitly deleted. Existing project networking is used without adding firewall rules.

```sh
python3 cloud/setup_vms.py
python3 cloud/setup_vms.py --apply
```

The first command prints the plan. The second is the authorized provisioning operation and requires a shell able to reach the Google Cloud API. It checks existing instance names before creating missing instances and reads back both final states. A failed API read is never treated as an empty project. Override the project, zone, machine type or run duration with the corresponding command-line options if needed.

Instances are named `oliver-lean-20261102-a` and `oliver-lean-20261102-b`. Startup readiness is separate from the VM's RUNNING status: inspect `/opt/oliver-lean/READY`, or `/var/log/oliver-lean-bootstrap.log` if setup fails. The helper prints the `gcloud compute ssh` readiness commands after observing two running VMs. Once ready, transfer `friedmann-missions.zip` and validate its targets using the guest's cached Mathlib; the package's dependency symlink must point to `/opt/oliver-lean/mathlib/.lake/packages`.

Specifications and flags were checked against [Google's machine-family documentation](https://docs.cloud.google.com/compute/docs/general-purpose-machines), [Linux VM creation guide](https://docs.cloud.google.com/compute/docs/create-linux-vm-instance), and [VM runtime-limit guide](https://docs.cloud.google.com/compute/docs/instances/limit-vm-runtime). Syntax and the offline plan were checked locally. Cloud creation, quota, live image availability, SSH connectivity and guest startup have not been verified.
