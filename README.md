
From: https://code.google.com/archive/p/inferno-spki/

A collection of C code, Limbo library modules, and Inferno file servers to allow SPKI proof sequences to be used for Inferno authentication.

Inferno's authentication is decentralised. Parties can have any number of public keys. The two parties to the authentication protocol present their chosen keys for the connection, each supported by a certificate provided by a common signer, usually determined by the service, and often run by the same administration. The signer associates a user name and a public key. Not all connections to a service require the same signer. Anyone can set up a signer (but only the owner of a service can make the service use it).

The existing Inferno scheme is naturally decentralised but does not easily scale. To address that, we turned to the decentralised but more scalable design of SDSI/SPKI. That will allow us to express arbitrary "speaks for" relations using SPKI certificates, which can then be presented to gain access to Inferno services. Amongst other things that provides a way to define group membership in a distributed Inferno system.

An important sub-project is to add Inferno's authentication scheme to the set supported by Plan 9's factotum (and similarly for Plan 9 Ports).

This software will become part of the main Inferno distribution, but it is convenient to develop it independently in this separate area.

This is a Google Summer-of-Code project.

