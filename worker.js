// worker for SingleBranchedGeometryEditor.html

******** License details **********************

 Copyright Klaus Hoffmeister
 2025 https://hofk.de/
 
 I am the copyright holder of this software.
 You may not physically or digitally host, display, distribute, or share this software (or any modified form thereof).
 You may not use this software in commercial or non-commercial products, websites, or projects.
 You may not sell this software, and you may not create NFTs from it.
 The software may be used for the private or non-commercial generation of geometries.
 The software and the generated geometries may be used for educational purposes
 and you may link to the software via a URL or source reference as part of your educational material.
 
***********************************************

const pi = Math.PI;
const p2i = pi / 2;
const rad = x => x * pi / 180;
const sin = x => Math.sin( x );
const cos = x => Math.cos( x );
const atan2 = ( y, x ) => Math.atan2( y, x );
const atan2Pi = ( x, y ) => atan2( y, x ) < 0 ? atan2( y, x ) + pi * 2 : atan2( y, x );
const sqrt = x => Math.sqrt( x );
const round = x => Math.round( x );
const n4 = ( r, s ) => round( pi * r / s / 2 );

onmessage = function( e ) {
      
    const param = e.data; 
    
    const gc = [];
    const buffers = [];
    
    for ( let j = 0; j < param.length; j ++ ) { // calculate cylinder values
         
        gc[ j ] = CalculateDeformableCylinderWithHoles( param[ j ] );
        
        buffers.push( gc[ j ].positions.buffer );
            
    }
    
    postMessage( gc, buffers );

}

function CalculateDeformableCylinderWithHoles( p ) {
    
// Algorithmus nach / Algorithm based on
// de: https://www2.mathematik.tu-darmstadt.de/~ehartmann/cdg0/cdg0n.pdf
// en: https://www2.mathematik.tu-darmstadt.de/~ehartmann/cdgen0104.pdf
    
    const gc = {};
    gc.type = 'Cyl';
    
    gc.d = p.triangleSide;    
    
    gc.btmDiff = p.btmDiff;
    gc.topDiff = p.topDiff;
    
    gc.div4 = n4( p.radius, gc.d );
    
    gc.height = p.height;
    
    gc.btm = -p.height / 2;
    gc.radiusBottom = p.radiusBottom !== undefined ? gc.d * n4( p.radiusBottom, gc.d ) * 2 / pi : Number.MAX_SAFE_INTEGER;
    gc.div4Btm =  p.radiusBottom !== undefined ? n4( p.radiusBottom, gc.d ) : Number.MAX_SAFE_INTEGER;  
    gc.phiBtm = p.phiBtm !== undefined ? p.phiBtm : 0;
    
    gc.top = p.height / 2;
    gc.radiusTop =  p.radiusTop !== undefined ? gc.d * n4( p.radiusTop, gc.d ) * 2 / pi : Number.MAX_SAFE_INTEGER;
    gc.div4Top = p.radiusTop !== undefined ? n4( p.radiusTop, gc.d ) : Number.MAX_SAFE_INTEGER ;
    gc.phiTop = p.phiTop !== undefined ? p.phiTop : 0;
    
    gc.holes = p.holes !== undefined ? p.holes : [];
    
    gc.detail = gc.div4 * 4; // division of the circle
    
    gc.radius = gc.d / sin( pi / gc.detail ) / 2; // cylinder radius, for external use as well
    
    const rAdpTop = gc.d / sin( pi / gc.div4Top / 4 ) / 2; // adaptation radius top
    gc.adjTop = rAdpTop - sqrt( rAdpTop * rAdpTop - gc.radius * gc.radius );   //adjustment top
    
    gc.cylTop = gc.top + gc.adjTop; // top with adjustment
    
    const rAdpBtm = gc.d / sin( pi / gc.div4Btm / 4 ) / 2; // adaptation radius bottom
    gc.adjBtm = rAdpBtm - sqrt( rAdpBtm * rAdpBtm - gc.radius * gc.radius ); // adjustment bottom
    
    gc.cylBtm = gc.btm - gc.adjBtm; // bottom with adjustment
    
    gc.fullHeight = gc.cylTop - gc.cylBtm; // cylinder height with adjustment parts top, bottom , - for external use as well
    
    gc.t  = [];  // relative height
    gc.ang = [];  // angle
    gc.vi = [];  // vertex index
    
    const dd = gc.d * gc.d;
    
    const squareLength = ( x,y,z ) => ( x*x + y*y + z*z );
    const length = ( x, y, z ) => ( sqrt( x * x + y * y + z * z ) );
    const lenXZ = ( x, z ) => ( sqrt( x * x + z * z ) );
    const prevFront = ( i ) => ( i !== 0 ? i - 1 : front.length - 1 );
    const nextFront  = ( i ) => ( i !== front.length - 1 ? i + 1 : 0 );
    const detYc0 = ( xa,ya,za, xb,yb,zb, xc,zc ) => ( xa*yb*zc + ya*zb*xc - za*yb*xc - ya*xb*zc ); // determinant yc = 0;
    
    let m; // index of the current front point
    let n; // number of new points
    let nT; // number of new triangles
    let nIns; // number of new points (after union or split)
    let dAng; // partial angle
    let len, d1, d2, d12; // lengths
    let iSplit, jSplit; // split front indices  
    let iUnite, jUnite, fUnite; // unite front indices, front number (to unite) 
    
    // points and vectors:
    let x, y, z, xp, yp, zp; // coordinates point and actual point p
    let x1, y1, z1, x2, y2, z2; // previous and next point to p in front
    let xn, zn; // normal, gradient  (cylinder: yn = 0)
    let xt1, yt1, zt1, xt2, yt2, zt2; // tangents
    let xs1, ys1, xs2, ys2; // p in tangential system (only x, y required)
    let xc, yc, zc; // actual point as center point for new points
    
    //  preparation
    
    indices = [];
    positions = [];
    
    let posIdx = 0;
    let indIdx = 0;
    let frontPosIdx, unionIdxA, unionIdxB, splitIdx;
    
    let front = []; // active front // front[ i ]: object { idx: 0, ang: 0 }
    let partFront = []; // separated part of the active front (to split)
    let insertFront = []; // new front points to insert into active front
    let fronts = []; // all fronts
    let partBounds = []; // bounding box of partFront [ xmin, xmax, ymin, ymax, zmin, zmax ]
    let boundings = []; // fronts bounding boxes
    let smallAngles = []; // new angles < 1.5
    
    let frontNo, frontStock;
    let unite = false;
    let split = false;
    
    // define fronts for cylinder boundaries y-axis
    
    frontNo = 0; // active front number
    frontStock = 0; // number of fronts still to be processed
    makeBoundaryFront( gc.btm, gc.div4Btm, -gc.phiBtm,  1 ); // ... , sign
    makeBoundaryFront( gc.top, gc.div4Top, -gc.phiTop, -1 ); // ... , sign
    
    gc.adapt = []; // array of arrays [ x0, y0, z0, rHole, div4, idx ], cylinder hole values for external use // new:  added start idx
    gc.holeIdx = []; // arrays of indices ( left and right hole positions ) // new  !!!!
    gc.hole_t = [];  // array of hole .t values  
    
    // define holes fronts
    
    for ( let i = 0; i < gc.holes.length; i ++ ) {
        
        if ( gc.holes[ i ].length === 5 ) {  // new!  with stretch y ,  append height  h    5 parameters 
            
            makeCircularHole( i );  // [ y, phi, r, stretch y, h ] 
            
        } else {
            
             // makePointsHole( i ); // points: [ y, phi, ... ]  //  even parameter count
            
        }
    
    }
    
    // makeBoundaryFront( gc.top, gc.div4Top, -gc.phiTop, -1 ); // ... , sign  //  in some older versions here
    
    frontNo = 0;
    front = fronts[ frontNo ];
    
    //////////////////  DEBUG triangles //////////////////////////////////
    //  let stp = 0;
    //////////////////////////////////////////////////////////////////////
    
    // ------ triangulation cycle -------------
    
    while ( frontStock > 0 ) {
        
        if (  !unite && !split ) { // triangulation on the front
            
            smallAngles = [];
            
            for ( let i = 0; i < front.length; i ++ ) {
                
                if( front[ i ].ang === 0 ) calculateFrontAngle( i ); // is to be recalculated (angle was set to zero)
                
            }
            
            m = getMinimalAngleIndex( ); // front angle
            makeNewTriangles( m );
                    
            if ( front.length > 9 && smallAngles.length === 0 ) {        
                
                checkDistancesToUnite( m );
                checkDistancesToSplit( m );
                
            }
            
            if ( front.length === 3 ) {
                
                makeLastTriangle( ); // last triangle closes the front
                chooseNextFront( );  // if aviable
                
            }
            
        } else { // unite the active front to another front or split the active front
            
            if ( unite ) {
                
                uniteFront(  m, iUnite, fUnite, jUnite );
                trianglesAtUnionPoints( );
                unite = false;
                                
            } else if ( split ) {
                
                splitFront( iSplit, jSplit );
                trianglesAtSplitPoints( );
                split = false;
                
            }
            
        }
         
    }
    
    gc.indices = new Uint32Array( indices );
    gc.positions = new Float32Array( positions );
    
    return gc;
     
    // .........  detail functions  .........
    
    function makeBoundaryFront( bd, divAdp, phiAdp, sign ) {
        
        // bd boundary, divAdp adaptation, phiAdp rotation of adaptive-deformed circle, rotation sign
        
        const rAdp = gc.d / sin( pi / divAdp / 4 ) / 2 ;
        
        let xmin, ymin, zmin, xmax, ymax, zmax;
        let x0, z0;
        
        fronts[ frontNo ] = [];
        boundings[ frontNo ] = []
        
        xmin = zmin = Infinity;
        ymin = ymax = bd;
        xmax = zmax = -Infinity;
        
        for ( let i = 0, phi = 0; i < gc.detail; i ++, phi += pi * 2 / gc.detail ) {
            
            // (adaptive-deformed) circle
            
            x = gc.radius * cos( phi );
            y = bd + sign * ( -rAdp +  sqrt( rAdp * rAdp - gc.radius * gc.radius * cos( phi ) * cos( phi ) ) );
                      
            const iCoo = ( i + gc.detail / 2 ) % gc.detail;  // angular displacement
            
            if( sign ===  1 ) y -= gc.btmDiff[ ( gc.detail - 1 ) - iCoo ]; // mirroring 
            if( sign === -1 ) y += gc.topDiff[ iCoo ]; 
            
            z = gc.radius * sin( sign * phi );
            
            if ( phiAdp !== 0 ) {
                
                x0 = x;
                z0 = z;
                
                // rotate around y axis 
                x = x0 * cos( phiAdp ) - z0 * sin( phiAdp ); 
                z = x0 * sin( phiAdp ) + z0 * cos( phiAdp );
            }
            
            gc.t.push( ( y - gc.cylBtm ) / gc.fullHeight ); // relative height ////////////////////////// new //////////////////////
            gc.ang.push( atan2Pi( z, x ) );                 // angle           ////////////////////////// new //////////////////////
            gc.vi.push( posIdx / 3 );                       // vertex index    ////////////////////////// new //////////////////////
            
            positions[ posIdx     ] = x;
            positions[ posIdx + 1 ] = y;
            positions[ posIdx + 2 ] = z;
            
            fronts[ frontNo ].push( { idx: posIdx / 3, ang: 0 } );
            
            xmin = x < xmin ? x : xmin;
            ymin = y < ymin ? y : ymin;
            zmin = z < zmin ? z : zmin;
            
            xmax = x > xmax ? x : xmax;
            ymax = y > ymax ? y : ymax;
            zmax = z > zmax ? z : zmax;
            
            posIdx += 3;
            
        }
        
        boundings[ frontNo ].push( xmin, xmax, ymin, ymax, zmin, zmax );
        
        frontNo ++;
        frontStock ++;
        
    }
    
    function makePointsHole( i ) {
        
        let  phi, count, xmin, ymin, zmin, xmax, ymax, zmax, xv2, yv2, zv2;
        
        xmin = ymin = zmin = Infinity;
        xmax = ymax = zmax = -Infinity;
        
        fronts[ frontNo ] = [];
        boundings[ frontNo ] = [];
        
        
        // ORIENTATION   AND  ° to rad ////////////////
        //phi = rad ( gc.holes[ i ][ 1 ] ) - p2i;
         phi = gc.holes[ i ][ 1 ] * pi / 180;
        
        x1 = gc.radius * cos( phi );
        y1 = gc.holes[ i ][ 0 ];
        z1 = -gc.radius * sin( phi );
        
        for ( let j = 1; j < gc.holes[ i ].length / 2 + 1; j ++ ) {
            
            positions[ posIdx     ] = x1;
            positions[ posIdx + 1 ] = y1;
            positions[ posIdx + 2 ] = z1;
            
            fronts[ frontNo ].push( { idx: posIdx / 3, ang: 0 } );
            
            xmin = x1 < xmin ? x1 : xmin;
            ymin = y1 < ymin ? y1 : ymin;
            zmin = z1 < zmin ? z1 : zmin;
            
            xmax = x1 > xmax ? x1 : xmax;
            ymax = y1 > ymax ? y1 : ymax;
            zmax = z1 > zmax ? z1 : zmax;
            
            posIdx += 3;
            
            phi = gc.holes[ i ][ j < gc.holes[ i ].length / 2 ? j * 2 + 1 : 1 ]; // 1 => connect to start
            
            x2 = gc.radius * cos( phi );
            y2 = gc.holes[ i ][ j < gc.holes[ i ].length / 2 ? j * 2 : 0 ]; // 0 => connect to start
            z2 = -gc.radius * sin( phi );
            
            xv2 = x2 - x1;
            yv2 = y2 - y1;
            zv2 = z2 - z1;
            
            len = length( xv2, yv2, zv2 );
            
            if ( len > gc.d ) {
                
                count = Math.ceil( len / gc.d );
                
                for ( let k = 1; k < count; k ++ ) {
                    
                    x = x1 + k * xv2 / count;
                    y = y1 + k * yv2 / count;
                    z = z1 + k * zv2 / count;
                    
                    len = lenXZ( x, z );   // to bring the point to the surface (radius * ..)
                    
                    x = gc.radius * x / len;
                    z = gc.radius * z / len;
                    
                    gc.t.push( ( y - gc.cylBtm ) / gc.fullHeight ); // relative height ////////////////////////// new ////////////////////
                    gc.ang.push( atan2Pi( z, x ) );                 // angle           ////////////////////////// new ////////////////////
                    gc.vi.push( posIdx / 3 );                       // vertex index    ////////////////////////// new ////////////////////
                    
                    positions[ posIdx     ] = x;
                    positions[ posIdx + 1 ] = y;
                    positions[ posIdx + 2 ] = z;
                        
                    fronts[ frontNo ].push( { idx: posIdx / 3, ang: 0 } );
                    
                    xmin = x < xmin ? x : xmin;
                    ymin = y < ymin ? y : ymin;
                    zmin = z < zmin ? z : zmin;
                    
                    xmax = x > xmax ? x : xmax;
                    ymax = y > ymax ? y : ymax;
                    zmax = z > zmax ? z : zmax;
                    
                    posIdx += 3;
                    
                }
                
            }
            
            x1 = x2;
            y1 = y2;
            z1 = z2;
            
        }
        
        boundings[ frontNo ].push( xmin, xmax, ymin, ymax, zmin, zmax );
        
        frontNo ++;
        frontStock ++;
        
    }
    
    function makeCircularHole( i ) {
        
        const stretchHoleY = gc.holes[ i ][ 3 ] * 1.2; // new:  stretch  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
        
        let x0, z0;
        
        const y0 = -gc.height / 2 + gc.height * gc.holes[ i ][ 0 ];  // new up,  based on bottom of main geometry
        
        // ORIENTATION   AND  ° to rad ////////////////
        //const phi = rad( gc.holes[ i ][ 1 ] ) - p2i;
        const phi = rad( gc.holes[ i ][ 1 ] );
        
        const div4 =  n4( gc.holes[ i ][ 2 ], gc.d );
        
        const countH = div4 * 4;
        
        let xmin, ymin, zmin, xmax, ymax, zmax;
        
        xmin = ymin = zmin = Infinity;
        xmax = ymax = zmax = -Infinity;
        
        const rHole =  1.12 * gc.d / sin( pi / countH ) / 2; // radius (x-deformed) cutting circle // !!! 1.12 to connect !!!
      
        // ORIENTATION ////////////////
        x0 = rHole * sin( phi + p2i );   
        z0 = rHole * cos( phi + p2i ); 
        // x0 = rHole * sin( phi );   
        // z0 = rHole * cos( phi ); 
        
        // cylinder hole values for external use
        gc.adapt.push( [ x0, y0, z0, rHole, div4, posIdx / 3 ] ); // new: added start idx = posIdx / 3 !!!!!!!!!!!!!!!!!!!!!!!!!
        
        fronts[ frontNo ] = [];
        boundings[ frontNo ] = [];
    
        for ( let j = countH - 1, alpha = 0 ; j > -1; j --, alpha += 2 * pi / countH ) {
            
            // (deformed) cutting circle in x-axis direction
            
            x0 = sqrt( gc.radius * gc.radius - rHole * rHole * cos( alpha ) * cos( alpha ) );
            y = y0 + rHole * stretchHoleY * sin( alpha );  // with stretch height
            z0 = rHole * cos( alpha );
             
            // rotate around y axis 
            x = x0 * cos( phi ) - z0 * sin( phi ); 
            z = -x0 * sin( phi ) - z0 * cos( phi );
            
            gc.t.push( ( y - gc.cylBtm ) / gc.fullHeight ); // relative height ////////////////////////// new //////////////////////
            gc.ang.push( atan2Pi( z, x ) );                 // angle           ////////////////////////// new //////////////////////
            gc.vi.push( posIdx / 3 );                       // vertex index    ////////////////////////// new //////////////////////
            
            
            // !!! new: indices of left and right hole positions !!!
            
            if ( j === countH - 1 ) { 
                
                gc.holeIdx.push( posIdx / 3 );
                gc.hole_t.push( ( y - gc.cylBtm ) / gc.fullHeight ); // hole center relative height 
                
            }
            
            if ( j === countH / 2 - 1 ) {
                    
                gc.holeIdx.push( posIdx / 3 );
            }
            
            positions[ posIdx     ] = x;
            positions[ posIdx + 1 ] = y;
            positions[ posIdx + 2 ] = z;
            
            fronts[ frontNo ].push( { idx: posIdx / 3, ang: 0 } );
            
            xmin = x < xmin ? x : xmin;
            ymin = y < ymin ? y : ymin;
            zmin = z < zmin ? z : zmin;
            
            xmax = x > xmax ? x : xmax;
            ymax = y > ymax ? y : ymax;
            zmax = z > zmax ? z : zmax;
            
            posIdx += 3;
            
        }
        
        boundings[ frontNo ].push( xmin, xmax, ymin, ymax, zmin, zmax );
        
        frontNo ++;
        frontStock ++;
        
    }
    
    function checkDistancesToUnite( m ) { // for new active front points
        
        let idxJ, xChk, yChk, zChk, ddUnite;
        let ddUniteMin = Infinity;
        unite = false;
        
        for ( let i = 0; i < insertFront.length; i ++ ) {
            
            getPoint( m + i );
            
            for ( let f = 0; f < fronts.length; f ++ ) { 
            
                if ( f !== frontNo ) {
                    
                    xChk = ( xp > boundings[ f ][ 0 ] - gc.d ) && ( xp < boundings[ f ][ 3 ] + gc.d );
                    yChk = ( yp > boundings[ f ][ 1 ] - gc.d ) && ( yp < boundings[ f ][ 4 ] + gc.d );
                    zChk = ( zp > boundings[ f ][ 2 ] - gc.d ) && ( zp < boundings[ f ][ 5 ] + gc.d );
                    
                    if (  xChk || yChk || zChk ) {
                        
                        for ( let j = 0; j < fronts[ f ].length; j ++ ) {
                            
                            idxJ = fronts[ f ][ j ].idx * 3;
                            
                            // Hint: here (2) is exceptionally point in other front!
                            x2 = positions[ idxJ ]; 
                            y2 = positions[ idxJ + 1 ];
                            z2 = positions[ idxJ + 2 ];
                            
                            ddUnite = squareLength ( x2 - xp, y2 - yp, z2 - zp );
                            
                            if ( ddUnite < dd && ddUnite < ddUniteMin ) {
                                
                                ddUniteMin = ddUnite; 
                                iUnite = i;
                                jUnite = j;
                                fUnite = f;
                                unite = true;
                                
                            }
                            
                        }
                        
                    }
                    
                }
                
            }
            
        }
        
    }
    
    function uniteFront( m, i, f, j ) {
        
        let tmp = [];
        
        tmp[ 0 ] = front.slice( 0, m + i + 1 );
        tmp[ 1 ] = fronts[ f ].slice( j , fronts[ f ].length );
        tmp[ 2 ] = fronts[ f ].slice( 0 , j + 1 );
        tmp[ 3 ] = front.slice( m + i, front.length );
        
        unionIdxA = m + i;
        unionIdxB = m + i + 1 + fronts[ f ].length
        
        front = [];
        
        for ( let t = 0; t < 4; t ++ ) {
            
            for ( let k = 0; k < tmp[ t ].length ; k ++ ) {
                
                front.push( tmp[ t ][ k ] );
                
            }
            
        }
        
        fronts[ f ] = []; // empty united front
        
        frontStock -= 1; // front is eliminated
        
    }
    
    function trianglesAtUnionPoints( ) {
        
        nIns = 0; // count inserted points
        
        calculateFrontAngle( unionIdxA );
        calculateFrontAngle( unionIdxA + 1 );
        
        if ( front[ unionIdxA ].ang < front[ unionIdxA + 1 ].ang ) {
            
            makeNewTriangles( unionIdxA );
            nIns += n - 1;
            calculateFrontAngle( unionIdxA + 1 + nIns );
            makeNewTriangles( unionIdxA + 1 + nIns );
            nIns += n - 1;
            
        } else {
            
            makeNewTriangles( unionIdxA + 1 );
            nIns += n - 1;
            calculateFrontAngle( unionIdxA );
            makeNewTriangles( unionIdxA );
            nIns += n - 1;
        }
        
        calculateFrontAngle( unionIdxB + nIns );
        calculateFrontAngle( unionIdxB + 1 + nIns );
        
        if ( front[ unionIdxB + nIns ].ang < front[ unionIdxB + 1 + nIns ].ang ) {
            
            makeNewTriangles( unionIdxB + nIns );
            nIns += n - 1;
            calculateFrontAngle( unionIdxB + 1 + nIns );
            makeNewTriangles( unionIdxB + 1 + nIns );
            
        } else {
            
            makeNewTriangles( unionIdxB + 1 + nIns );
            calculateFrontAngle( unionIdxB + nIns );
            makeNewTriangles( unionIdxB + nIns );
            
        }
        
    }
    
    function checkDistancesToSplit( m ) { // for new active front points
        
        let mj, mjIdx, ddSplit;
        let ddSplitMin = Infinity;
        split = false;
            
        for ( let i = 0; i < front.length ; i ++ ) {
            
            for ( let j = 0; j < n; j ++ ) { // check n new points (insertFront)
            
                mj = m + j;
                
                // except new points themselves and neighbor points
                if ( Math.abs( i - mj ) > 3 && Math.abs( i - mj ) < front.length - 3 ) {
                    
                    mjIdx = front[ mj ].idx * 3;
                    
                    // Hint: here (1) is exceptionally new point in the front!
                    x1 = positions[ mjIdx ]; 
                    y1 = positions[ mjIdx + 1 ];
                    z1 = positions[ mjIdx + 2 ];
                    
                    getPoint( i );
                    
                    ddSplit = squareLength ( x1 - xp, y1 - yp, z1 - zp );
                    
                    if ( ddSplit < dd && ddSplit < ddSplitMin ) {
                        
                        ddSplitMin = ddSplit;
                        iSplit = i;
                        jSplit = mj;
                        split = true; 
                        
                    }
                    
                }
                
            }
            
        }
        
    }
    
    function splitFront( iSplit, jSplit ) {
        
        let k;
        
        front[ iSplit ].ang = 0;
        front[ jSplit ].ang = 0;
        
        if ( iSplit > jSplit )  { // swap
            
            k = jSplit;
            jSplit = iSplit;
            iSplit = k;
            
        } 
        
        splitIdx = iSplit;    // lower index
        
        partFront = [];
        
        // to duplicate
        let frontI = front[ iSplit ];        
        let frontJ = front[ jSplit ];
        
        partFront = front.splice( iSplit + 1, jSplit - iSplit - 1 );
        partFront.unshift( frontI );
        partFront.push( frontJ );
        
        fronts.push( partFront );
        
        partFrontBounds( );
        
        frontStock += 1; // new front created
        
    }
    
    function trianglesAtSplitPoints( ) {
        
        nIns = 0; // count inserted points
        
        let idx0 = splitIdx; // splitIdx is the lower index 
        let idx1 = splitIdx + 1;
        
        calculateFrontAngle( idx0 );
        calculateFrontAngle( idx1 );
        
        if ( front[ idx1 ].ang < front[ idx0 ].ang ){
            
            makeNewTriangles( idx1 );
            nIns += n - 1;
            calculateFrontAngle( idx0 );
            makeNewTriangles( idx0 );
            
        } else {
            
            makeNewTriangles( idx0 );
            nIns += n - 1;
            calculateFrontAngle( idx1 + nIns );
            makeNewTriangles( idx1 + nIns );
            
        }
        
    }
    
    function getMinimalAngleIndex( ) {
        
        let angle = Infinity;
        let m;
        
        for ( let i = 0; i < front.length; i ++ ) {
            
            if( front[ i ].ang < angle  ) {
                
                angle = front[ i ].ang ;
                m = i;
                
            }
            
        }
    
        return m;
        
    }
    
    function makeNewTriangles( m ) {
        
        //    m:  minimal angle (index)
        
        insertFront = []; // new front points
        
        nT = Math.floor( 3 * front[ m ].ang / pi ) + 1; // number of new triangles
        
        dAng = front[ m ].ang / nT;
        
        getSystemAtPoint( m );
        getNextPoint( m );
        
        d1 = length( x1 - xp, y1 - yp, z1 - zp );
        d2 = length( x2 - xp, y2 - yp, z2 - zp );    
        d12 = length( x2 - x1, y2 - y1, z2 - z1 );
        
        // correction of dAng, nT in extreme cases
        
        if ( dAng < 0.8 && nT > 1 ) {
            
            nT --;
            dAng = front[ m ].ang / nT;
            
        }
        
        if ( dAng > 0.8 && nT === 1 && d12 > 1.25 * gc.d ) {
            
            nT = 2; 
            dAng = front[ m ].ang / nT;
            
        }
        
        if ( d1 * d1 < 0.2 * dd ||  d2 * d2 < 0.2 * dd  ) {
            
            nT = 1;
            
        }
        
        n = nT - 1;  // n number of new points
            
        if ( n === 0 ) { // one triangle
            
            indices[ indIdx     ] = front[ m ].idx;
            indices[ indIdx + 1 ] = front[ prevFront( m ) ].idx; 
            indices[ indIdx + 2 ] = front[ nextFront( m ) ].idx;
            
            indIdx += 3;
            
            ///////////////  DEBUG triangles  //////////////////////
             // stp ++;
            ////////////////////////////////////////////////////////
                    
            front[ prevFront( m ) ].ang = 0;        
            front[ nextFront( m ) ].ang = 0;            
            
            front.splice( m, 1 ); // delete point with index m from the front
                
        } else { // more then one triangle
            
            xc = xp;
            yc = yp;
            zc = zp;
            
            for ( let i = 0,  phi = dAng; i < n; i ++, phi += dAng ) {
                
                xp = xc + cos( phi ) * gc.d * xt1 + sin( phi ) * gc.d * xt2; 
                yp = yc + cos( phi ) * gc.d * yt1 + sin( phi ) * gc.d * yt2;
                zp = zc + cos( phi ) * gc.d * zt1 + sin( phi ) * gc.d * zt2;
                
                len = lenXZ( xp, zp );   // to bring the point to the surface (radius * ..)
                
                x = gc.radius * xp / len; ////////////////////////// new //////////////////////
                y = yp;                   ////////////////////////// new //////////////////////
                z = gc.radius * zp / len; ////////////////////////// new //////////////////////
                
                gc.t.push( ( y - gc.cylBtm ) / gc.fullHeight ); // relative height  ////////////////////////// new //////////////////////
                gc.ang.push( atan2Pi( z, x ) );                 // angle            ////////////////////////// new //////////////////////
                gc.vi.push( posIdx / 3 );                       // vertex index     ////////////////////////// new //////////////////////
                
                positions[ posIdx     ] = x;
                positions[ posIdx + 1 ] = y;
                positions[ posIdx + 2 ] = z;
                
                insertFront.push( { idx: posIdx / 3, ang: 0 } );
                
                posIdx += 3;                
                        
            }    
            
            indices[ indIdx     ] = front[ m ].idx;
            indices[ indIdx + 1 ] = front[ prevFront( m ) ].idx 
            indices[ indIdx + 2 ] = insertFront[ 0 ].idx;
            
            indIdx += 3;
            
            ///////////////  DEBUG  triangles  /////////////////////
             // stp ++;
            ////////////////////////////////////////////////////////
            
            front[ prevFront( m ) ].ang = 0;
            
            for ( let i = 0; i < n - 1; i ++ ) {
                
                indices[ indIdx     ] = front[ m ].idx;
                indices[ indIdx + 1 ] = insertFront[ i ].idx;
                indices[ indIdx + 2 ] = insertFront[ i + 1 ].idx;
                
                indIdx += 3;
                
                ///////////////  DEBUG triangles  //////////////////////
                // stp ++;
                ////////////////////////////////////////////////////////
                
            }
            
            indices[ indIdx     ] = front[ m ].idx;
            indices[ indIdx + 1 ] = insertFront[ n - 1 ].idx;
            indices[ indIdx + 2 ] = front[ nextFront( m ) ].idx;
            
            front[ nextFront( m ) ].ang = 0;
            
            indIdx += 3;
            
            ///////////////  DEBUG triangles  //////////////////////
             // stp ++;
            ////////////////////////////////////////////////////////
                    
            replaceFront( m, insertFront ); // replaces front[ m ] with new points
            
        }
        
    }
    
    function makeLastTriangle( ) {
        
        indices[ indIdx     ] = front[ 2 ].idx;
        indices[ indIdx + 1 ] = front[ 1 ].idx 
        indices[ indIdx + 2 ] = front[ 0 ].idx;
        
        indIdx += 3;
        
        ///////////////  DEBUG triangles  //////////////////////
         // stp ++;
        ////////////////////////////////////////////////////////
        
        front = [];
        
        fronts[ frontNo ] = [];
        
        frontStock -= 1; // close front
        
    }
    
    function chooseNextFront( ) {
        
        if ( frontStock > 0 ) {
            
            for ( let i = 0; i < fronts.length; i ++ ) {
                
                if ( fronts[ i ].length > 0 ) {
                    
                    frontNo = i;
                    break;
                    
                }
                
            }
            
            front = fronts[ frontNo ];
            
            smallAngles = [];
            
            for ( let i = 0; i < front.length; i ++ ) {
                
                calculateFrontAngle( i ); // recalculate angles of next front
                 
            }
            
        }
        
    }
    
    function atan2PI( x, y ) {
        
        let phi = Math.atan2( y, x );
        
        if ( phi < 0 ) phi = phi + pi * 2;
        
        return phi;
            
    }
    
    function coordTangentialSystem( ) {
        
        let det = detYc0( xt1, yt1, zt1, xt2, yt2, zt2, xn, zn ); // cylinder:  yn=yc=0
        
        xs1 = detYc0( x1 - xp, y1 - yp, z1 - zp, xt2, yt2, zt2, xn, zn ) / det;
        ys1 = detYc0( xt1, yt1, zt1, x1 - xp, y1 - yp, z1 - zp, xn, zn ) / det;
        //zs1  not needed
        
        xs2 = detYc0( x2 - xp, y2 - yp, z2 - zp, xt2, yt2, zt2, xn, zn ) / det;
        ys2 = detYc0( xt1, yt1, zt1, x2 - xp, y2 - yp, z2 - zp, xn, zn ) / det;
        //zs2 not needed
        
    }
    
    function calculateFrontAngle( i ) {
        
        let ang1, ang2;
        
        getSystemAtPoint( i );
        getNextPoint( i );
        
        coordTangentialSystem( );
        
        ang1 = atan2PI( xs1, ys1 );
        ang2 = atan2PI( xs2, ys2 );
        
        if ( ang2 < ang1 )  ang2 += pi * 2;
        
        front[ i ].ang  = ang2 - ang1;
        
        if ( front[ i ].ang < 1.5 ) smallAngles.push( i );
        
    }
    
    function partFrontBounds( ) {
        
        let idx, xmin, ymin, zmin, xmax, ymax, zmax;
        
        partBounds = [];
        
        xmin = ymin = zmin = Infinity;
        xmax = ymax = zmax = -Infinity;
        
        for( let i = 0; i < partFront.length; i ++ ) {
            
            idx = partFront[ i ].idx * 3;
            
            x = positions[ idx ]; 
            y = positions[ idx + 1 ];
            z = positions[ idx + 2 ];
            
            xmin = x < xmin ? x : xmin; 
            ymin = y < ymin ? y : ymin;
            zmin = z < zmin ? z : zmin;
            
            xmax = x > xmax ? x : xmax;
            ymax = y > ymax ? y : ymax;
            zmax = z > zmax ? z : zmax;
            
        }
        
        partBounds.push( xmin, ymin, zmin, xmax, ymax, zmax );
        
        boundings.push( partBounds );
        
    }
    
    function replaceFront( m, fNew ) {
        
        let rear = front.splice( m, front.length - m );
        
        for ( let i = 0; i < fNew.length; i ++ ) {
            
            front.push( fNew[ i ] ); // new front points
            
        }
        
        for ( let i = 1; i < rear.length; i ++ ) { // i = 1: without old front point m 
            
            front.push( rear[ i ] );
            
        }
        
    }
    
    function getSystemAtPoint( i ) {
        
        getPrevPoint( i );
        getPoint( i );
        
        len = lenXZ( xp, zp );
        xn = xp / len;
        zn = zp / len;
        
        // cross,  cylinder:  yn=0  
        
        xt2 = -zn * ( y1 - yp );
        yt2 = zn * ( x1 - xp ) - xn * ( z1 - zp );
        zt2 = xn * ( y1 - yp );
        
        len = length( xt2, yt2, zt2 ); // to normalize
        
        xt2 = xt2 / len;
        yt2 = yt2 / len;
        zt2 = zt2 / len;
        
        // cross
        xt1 = yt2 * zn;
        yt1 = zt2 * xn - xt2 * zn;
        zt1 = -yt2 * xn;
        
    }
    
    function getPrevPoint( i ) {
        
        frontPosIdx = front[ prevFront( i ) ].idx * 3;
        
        x1 = positions[ frontPosIdx ]; 
        y1 = positions[ frontPosIdx + 1 ];
        z1 = positions[ frontPosIdx + 2 ];
        
    }
    
    function getPoint( i ) {
        
        frontPosIdx = front[ i ].idx * 3;
        
        xp = positions[ frontPosIdx ]; 
        yp = positions[ frontPosIdx + 1 ];
        zp = positions[ frontPosIdx + 2 ];
        
    }
    
    function getNextPoint( i ) {
        
        frontPosIdx = front[ nextFront( i ) ].idx * 3;
        
        x2 = positions[ frontPosIdx ];
        y2 = positions[ frontPosIdx + 1 ];
        z2 = positions[ frontPosIdx + 2 ];
        
    }

} // function CalculateDeformableCylinderWithHoles